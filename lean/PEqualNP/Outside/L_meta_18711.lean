import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18711

open PEqualNP.CircuitLowerBounds

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem step (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (w w' : List Bool) (k : ℕ) (v : Bool)
    (hw : w.length = x1 + k) (hw' : w'.length = x2 + k)
    (h : ∀ i, w'.getD (f i) false = w.getD i false) (i : ℕ) :
    (w' ++ [v]).getD (f i) false = (w ++ [v]).getD i false := by
  have hi := h i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at hi ⊢
  by_cases c : i < x1
  · have := hf1 i c
    have a1 : f i < w'.length := by omega
    have a2 : i < w.length := by omega
    simp only [a1, a2, ite_true]
    exact hi
  · have e := hf2 i (by omega)
    by_cases d : i < x1 + k
    · have a1 : f i < w'.length := by omega
      have a2 : i < w.length := by omega
      simp only [a1, a2, ite_true]
      exact hi
    · have a1 : ¬ f i < w'.length := by omega
      have a2 : ¬ i < w.length := by omega
      have a3 : f i - w'.length = i - w.length := by omega
      simp only [a1, a2, ite_false, a3]

theorem main (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (gs : List Gate) :
    ∀ (w w' : List Bool) (k : ℕ), w.length = x1 + k → w'.length = x2 + k →
    (∀ i, w'.getD (f i) false = w.getD i false) → ∀ i,
    ((gs.map (rg f)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (f i) false
    = (gs.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
  induction gs with
  | nil => intro w w' k _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' k hw hw' h i
    simp only [List.map_cons, List.foldl_cons]
    have e : (rg f g).op.eval ((rg f g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact h a
    rw [e]
    apply ih _ _ (k + 1)
    · simp [hw]; omega
    · simp [hw']; omega
    · exact step x1 x2 f hf1 hf2 w w' k _ hw hw' h

end PEqualNP.Outside.L_meta_18711

open PEqualNP.Outside.L_meta_18711 PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_18711 : (∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x6 : ℕ), Function.Injective x2 → PEqualNP.TopForm.IsAO2 x1 x3 → (∀ x9 ∈ x3.gates, x9.inputs.Nodup) → x3.output = x1 + x4 → x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x12.size = x3.size ∧ PEqualNP.TopForm.IsAO2 x1 x12 ∧ (∀ x15 ∈ x12.gates, x15.inputs.Nodup) ∧ x12.output = x1 + x4 ∧ x12.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x13, x14] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x15 : Fin x1 → Bool), x12.eval (List.ofFn x15) = x3.eval (List.ofFn (x15 ∘ x2)) ∧ (x12.wires (List.ofFn x15)).getD x13 Bool.false = (x3.wires (List.ofFn (x15 ∘ x2))).getD x5 Bool.false ∧ (x12.wires (List.ofFn x15)).getD x14 Bool.false = (x3.wires (List.ofFn (x15 ∘ x2))).getD x6 Bool.false) := by
  intro n f C j a b hf hao hnd ho hgate
  let W (i : ℕ) : ℕ := if h : i < n then (f ⟨i,h⟩).val else i
  have low (i : ℕ) (hi : i < n) : W i < n := by simpa [W, hi] using (f ⟨i,hi⟩).isLt
  have high (i : ℕ) (hi : n ≤ i) : W i = i := dif_neg (by omega)
  have inj : Function.Injective W := by
    intro i k he
    by_cases hi : i < n <;> by_cases hk : k < n
    · simp only [W, dif_pos hi, dif_pos hk] at he
      exact congrArg Fin.val (hf (Fin.ext he))
    · have := low i hi
      rw [high k (by omega)] at he
      omega
    · have := low k hk
      rw [high i (by omega)] at he
      omega
    · rwa [high i (by omega), high k (by omega)] at he
  let D : Circuit := ⟨C.gates.map (rg W), C.output⟩
  have len : D.gates.length = C.gates.length := by simp [D]
  have atGate (k : ℕ) (hk : k < C.gates.length) : gateAt D k = rg W (gateAt C k) := by
    rw [gateAt, gateAt, List.getD_eq_getElem _ _ (by omega : k < D.gates.length), List.getD_eq_getElem _ _ hk]
    simp [D]
  have ao : IsAO2 n D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact hao.1 q hq
    · intro k hk i hi
      have hk' : k < C.gates.length := by omega
      rw [atGate k hk'] at hi
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hi
      have := hao.2.1 k hk' l hl
      by_cases h : l < n
      · have := low l h
        omega
      · rw [high l (by omega)]
        assumption
    · intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      simpa [rg] using hao.2.2 q hq
  refine ⟨D, W a, W b, len, ao, ?_, ho, ?_, ?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact List.Nodup.map inj (hnd q hq)
  · change (C.gates.map (rg W))[j]? = _
    simp only [List.getElem?_map, hgate, Option.map_some, rg, List.map_cons, List.map_nil]
  · intro x
    have init (i : ℕ) : (List.ofFn x).getD (W i) false = (List.ofFn (x ∘ f)).getD i false := by
      by_cases hi : i < n
      · simp [W, hi, Function.comp_def]
      · rw [high i (by omega), List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi)]
    have val (i : ℕ) : (D.wires (List.ofFn x)).getD (W i) false =
        (C.wires (List.ofFn (x ∘ f))).getD i false :=
      main n n W low (fun k hk => by rw [high k hk]; omega) C.gates _ _ 0 (by simp) (by simp) init i
    refine ⟨?_,val a,val b⟩
    have he := val C.output
    rw [high C.output (by omega)] at he
    exact he
