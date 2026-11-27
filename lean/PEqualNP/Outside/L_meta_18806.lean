import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18806.Helpers

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

theorem natstep (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (w w' : List ℕ) (k : ℕ) (v : ℕ)
    (hw : w.length = x1 + k) (hw' : w'.length = x2 + k)
    (h : ∀ i, w'.getD (f i) 0 = w.getD i 0) (i : ℕ) :
    (w' ++ [v]).getD (f i) 0 = (w ++ [v]).getD i 0 := by
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

theorem natmain (x1 x2 : ℕ) (f : ℕ → ℕ) (hf1 : ∀ i, i < x1 → f i < x2)
    (hf2 : ∀ i, x1 ≤ i → f i = i - x1 + x2) (gs : List Gate) :
    ∀ (w w' : List ℕ) (k : ℕ), w.length = x1 + k → w'.length = x2 + k →
    (∀ i, w'.getD (f i) 0 = w.getD i 0) → ∀ i,
    ((gs.map (rg f)).foldl
      (fun w g => w ++ [g.lineDegree w]) w').getD (f i) 0
    = (gs.foldl
      (fun w g => w ++ [g.lineDegree w]) w).getD i 0 := by
  induction gs with
  | nil => intro w w' k _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' k hw hw' h i
    simp only [List.map_cons, List.foldl_cons]
    have e : (rg f g).lineDegree w'
        = g.lineDegree w := by
      have hm : (g.inputs.map fun i => w'.getD (f i) 0) = (g.inputs.map fun i => w.getD i 0) := by
        apply List.map_congr_left
        intro a _
        exact h a
      simp only [rg,Gate.lineDegree,List.map_map,Function.comp_def]
      rw [hm]
      by_cases hop : g.op = GateOp.and <;> simp [hop]
    rw [e]
    apply ih _ _ (k + 1)
    · simp [hw]; omega
    · simp [hw']; omega
    · exact natstep x1 x2 f hf1 hf2 w w' k _ hw hw' h


open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
theorem permutation (n : ℕ) (C : Circuit) (e : Equiv.Perm (Fin n))
    (hao : PEqualNP.TopForm.IsAO2 n C) (hnd : ∀ g ∈ C.gates,g.inputs.Nodup) :
    ∃ D : Circuit, D.size = C.size ∧ PEqualNP.TopForm.IsAO2 n D ∧
      (∀ g ∈ D.gates,g.inputs.Nodup) ∧
      (∀ x : Fin n → Bool,D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e))) ∧
      ∀ i : Fin n,D.lineDeg n {(e i).val} = C.lineDeg n {i.val} := by
  let f : Fin n → Fin n := e
  have hf : Function.Injective f := e.injective
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
  let D : Circuit := ⟨C.gates.map (rg W), W C.output⟩
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
  refine ⟨D,len,ao,?_,?_,?_⟩
  · intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact List.Nodup.map inj (hnd q hq)
  · intro x
    have init (i : ℕ) : (List.ofFn x).getD (W i) false = (List.ofFn (x ∘ f)).getD i false := by
      by_cases hi : i < n
      · simp [W, hi, Function.comp_def]
      · rw [high i (by omega), List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi)]
    have val (i : ℕ) : (D.wires (List.ofFn x)).getD (W i) false =
        (C.wires (List.ofFn (x ∘ f))).getD i false :=
      main n n W low (fun k hk => by rw [high k hk]; omega) C.gates _ _ 0 (by simp) (by simp) init i
    exact val C.output
  · intro i
    have init (j : ℕ) :
        ((List.range n).map fun k => if k ∈ ({(e i).val} : Finset ℕ) then 1 else 0).getD (W j) 0 =
        ((List.range n).map fun k => if k ∈ ({i.val} : Finset ℕ) then 1 else 0).getD j 0 := by
      by_cases hj : j < n
      · have hw : W j < n := low j hj
        have heq : W j = (e i).val ↔ j = i.val := by
          constructor
          · intro h
            have : e ⟨j,hj⟩ = e i := Fin.ext (by simpa [W,hj,f] using h)
            exact congrArg Fin.val (e.injective this)
          · intro h
            subst j
            simp [W,f]
        simp [List.getD_eq_getElem?_getD,hj,hw,heq]
      · rw [high j (by omega),List.getD_eq_default _ _ (by simp;omega),
          List.getD_eq_default _ _ (by simp;omega)]
    exact natmain n n W low (fun k hk => by rw [high k hk];omega) C.gates _ _ 0
      (by simp) (by simp) init C.output

end PEqualNP.Outside.L_meta_18806.Helpers


theorem PEqualNP.Outside.L_meta_18806 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x5 ∈ x2.gates, x5.inputs.Nodup) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2.size ∧ PEqualNP.TopForm.IsAO2 x1 x6 ∧ (∀ x7 ∈ x6.gates, x7.inputs.Nodup) ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn (x7 ∘ ⇑x3))) ∧ ∀ (x7 : Fin x1), x6.lineDeg x1 {↑(x3 x7)} = x2.lineDeg x1 {↑x7}) := by
  exact PEqualNP.Outside.L_meta_18806.Helpers.permutation
