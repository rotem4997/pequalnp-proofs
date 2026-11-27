import PEqualNP.MetaComplexity.Helpers.LowMergeWires

/-!
# Facts F1 to F3 on the restricted inputs at one line

`V C w g pts` is the value of wire `g` on the restricted input at line `w` with points `pts`.
-/

namespace PEqualNP.MetaComplexity.LowMergeProof

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

/-- Value of wire `g` on the restricted input at `w`. -/
def V {P L : ℕ} (C : Circuit) (w : Fin L) (g : ℕ) (pts : Fin P → Bool) : Bool :=
  wireVal C (restrictInput P L w pts) g

/-- The indicator of one point. -/
def ind {P : ℕ} (p : Fin P) : Fin P → Bool := fun q => decide (q = p)

theorem restrict_length (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) :
    (restrictInput P L w pts).length = P + L := by
  simp [restrictInput]

theorem restrict_getD_lt (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) (i : ℕ) (h : i < P) :
    (restrictInput P L w pts).getD i false = pts ⟨i, h⟩ := by
  unfold restrictInput
  rw [List.getD_append _ _ _ _ (by simp; exact h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem restrict_getD_ge (P L : ℕ) (w : Fin L) (pts pts' : Fin P → Bool) (i : ℕ) (h : P ≤ i) :
    (restrictInput P L w pts).getD i false = (restrictInput P L w pts').getD i false := by
  unfold restrictInput
  rw [List.getD_append_right _ _ _ _ (by simp; exact h),
    List.getD_append_right _ _ _ _ (by simp; exact h)]
  simp

theorem alive_mem {P L : ℕ} (C : Circuit) (w : Fin L) (g : ℕ) (p : Fin P) :
    p ∈ aliveSet P L C g w ↔ V C w g (ind p) = true := by
  unfold aliveSet V pointLineInput ind
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem lineSum_ind {P L : ℕ} (inc : Fin P → Fin L → Bool) (w : Fin L) (p : Fin P) :
    lineSum P L inc w (ind p) = inc p w := by
  unfold lineSum ind
  by_cases h : inc p w = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    rw [h]; simp only [decide_eq_false_iff_not]
    rintro ⟨q, hq, hq'⟩
    simp only [decide_eq_true_eq] at hq'
    subst hq'; simp [h] at hq

theorem lineSum_false {P L : ℕ} (inc : Fin P → Fin L → Bool) (w : Fin L) :
    lineSum P L inc w (fun _ => false) = false := by
  simp [lineSum]

theorem isLow_iff {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    IsLow P L inc C g w ↔ ∀ pts, V C w g pts = true → lineSum P L inc w pts = true := Iff.rfl

/-- A low wire's alive set lies on the line. -/
theorem alive_sub_line {P L : ℕ} (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ)
    (w : Fin L) (h : IsLow P L inc C g w) :
    aliveSet P L C g w ⊆ Finset.univ.filter (fun p : Fin P => inc p w = true) := by
  intro p hp
  rw [alive_mem] at hp
  have := h _ hp
  rw [lineSum_ind] at this
  simp [this]

theorem V_big {P L : ℕ} (C : Circuit) (w : Fin L) (g : ℕ) (pts : Fin P → Bool)
    (h : P + L + C.gates.length ≤ g) : V C w g pts = false := by
  unfold V wireVal
  rw [List.getD_eq_default]
  rw [wires_length, restrict_length]; exact h

theorem V_input_lt {P L : ℕ} (C : Circuit) (w : Fin L) (g : ℕ) (pts : Fin P → Bool)
    (h : g < P) : V C w g pts = pts ⟨g, h⟩ := by
  unfold V wireVal
  rw [wires_input _ _ _ (by rw [restrict_length]; omega), restrict_getD_lt _ _ _ _ _ h]

theorem V_input_ge {P L : ℕ} (C : Circuit) (w : Fin L) (g : ℕ) (pts pts' : Fin P → Bool)
    (h : P ≤ g) (h' : g < P + L) : V C w g pts = V C w g pts' := by
  unfold V wireVal
  rw [wires_input _ _ _ (by rw [restrict_length]; omega),
    wires_input _ _ _ (by rw [restrict_length]; omega), restrict_getD_ge _ _ _ _ _ _ h]

/-- Read value: an operand at or above the gate reads `false`. -/
def R {P L : ℕ} (C : Circuit) (w : Fin L) (t i : ℕ) (pts : Fin P → Bool) : Bool :=
  if i < t then V C w i pts else false

theorem V_gate {P L : ℕ} (C : Circuit) (w : Fin L) (j : ℕ) (hj : j < C.gates.length)
    (pts : Fin P → Bool) :
    V C w (P + L + j) pts
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => R C w (P + L + j) i pts) := by
  unfold V wireVal
  have := wires_gate C (restrictInput P L w pts) j hj
  rw [restrict_length] at this
  rw [this]
  rfl

theorem V_mono {P L : ℕ} (C : Circuit) (hC : IsMonotoneCircuit C) (w : Fin L) (g : ℕ)
    (pts pts' : Fin P → Bool) (h : ∀ p, pts p = true → pts' p = true) :
    V C w g pts = true → V C w g pts' = true := by
  unfold V wireVal
  apply wires_mono C hC _ _ (by rw [restrict_length, restrict_length])
  intro i hi
  by_cases hiP : i < P
  · rw [restrict_getD_lt _ _ _ _ _ hiP] at hi ⊢
    exact h _ hi
  · rw [restrict_getD_ge _ _ _ _ pts _ (by omega)]; exact hi

end PEqualNP.MetaComplexity.LowMergeProof
