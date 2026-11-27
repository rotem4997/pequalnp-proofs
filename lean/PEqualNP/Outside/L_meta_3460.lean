import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3460

open PEqualNP.CircuitLowerBounds

-- one evaluation step of a circuit
def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

-- the shifted copy of a gate
def shG (n k : ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + k) }

theorem foldl_length (gs : List Gate) : ∀ (A : List Bool),
    (gs.foldl stepF A).length = A.length + gs.length := by
  induction gs with
  | nil => intro A; simp
  | cons g gs ih =>
    intro A
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [stepF]
    omega

theorem foldl_prefix (gs : List Gate) : ∀ (A : List Bool) (i : ℕ), i < A.length →
    (gs.foldl stepF A).getD i false = A.getD i false := by
  induction gs with
  | nil => intro A i _; simp
  | cons g gs ih =>
    intro A i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [stepF]; omega)]
    simp only [stepF]
    rw [List.getD_append _ _ _ _ hi]

theorem foldl_shift (n k : ℕ) (gs : List Gate) : ∀ (A B : List Bool), n ≤ A.length →
    B.length = A.length + k →
    (∀ i, B.getD (if i < n then i else i + k) false = A.getD i false) →
    (∀ i, ((gs.map (shG n k)).foldl stepF B).getD (if i < n then i else i + k) false
      = (gs.foldl stepF A).getD i false) := by
  induction gs with
  | nil => intro A B _ _ h; simpa using h
  | cons g gs ih =>
    intro A B hn hB h
    simp only [List.map_cons, List.foldl_cons]
    have hv : (shG n k g).op.eval ((shG n k g).inputs.map fun i => B.getD i false)
        = g.op.eval (g.inputs.map fun i => A.getD i false) := by
      simp only [shG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro w _
      exact h w
    apply ih
    · simp [stepF]; omega
    · simp [stepF]; omega
    · intro i
      simp only [stepF]
      rw [hv]
      rcases lt_trichotomy i A.length with hi | hi | hi
      · have hs : (if i < n then i else i + k) < B.length := by
          split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ hi, h i]
      · have hs : (if i < n then i else i + k) = B.length := by
          split_ifs <;> omega
        rw [hs, List.getD_append_right _ _ _ _ (le_refl _),
          List.getD_append_right _ _ _ _ (le_of_eq hi.symm)]
        simp [hi]
      · have hs : B.length + 1 ≤ (if i < n then i else i + k) := by
          split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3460

theorem PEqualNP.Outside.L_meta_3460 : ∀ (n : ℕ) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool), (∀ i < G0.length, ∀ w ∈ (G0.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w < n + i) → (∀ i : ℕ, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (if i < n then i else i + G0.length) false = (C.wires (List.ofFn x)).getD i false) ∧ (∀ i < G0.length, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false = ((⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false) := by
  intro n G0 C x _
  have hW : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (y : List Bool),
      D.wires y = D.gates.foldl PEqualNP.Outside.L_meta_3460.stepF y := fun _ _ => rfl
  have hD : (G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)))
      = G0 ++ C.gates.map (PEqualNP.Outside.L_meta_3460.shG n G0.length) := rfl
  simp only [hW, hD, List.foldl_append]
  have hlen : (G0.foldl PEqualNP.Outside.L_meta_3460.stepF (List.ofFn x)).length
      = n + G0.length := by
    rw [PEqualNP.Outside.L_meta_3460.foldl_length]; simp
  refine ⟨?_, ?_⟩
  · apply PEqualNP.Outside.L_meta_3460.foldl_shift
    · simp
    · rw [hlen]; simp
    · intro i
      split_ifs with hi
      · rw [PEqualNP.Outside.L_meta_3460.foldl_prefix _ _ _ (by simpa using hi)]
      · rw [List.getD_eq_default _ _ (by rw [hlen]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  · intro i hi
    rw [PEqualNP.Outside.L_meta_3460.foldl_prefix _ _ _ (by rw [hlen]; omega)]
