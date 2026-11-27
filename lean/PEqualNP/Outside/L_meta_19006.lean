import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19006.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma append_mono (x y : List Bool) (a b : Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (x ++ [a]).getD i false = true → (y ++ [b]).getD i false = true := by
  intro i
  by_cases hi : i < x.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hl]
    cases he : i - y.length <;> simp_all

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (h : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro hx i hi
    exact h i (hx i hi)
  · simp only [hg, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h i hx⟩

lemma run_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i, (run gs (x ++ [_])).getD i false = true →
      (run gs (y ++ [_])).getD i false = true
    apply ih (fun q hq => hm q (List.mem_cons_of_mem g hq)) _ _ (by simp [hl])
    exact append_mono x y _ _ hl h (gate_mono g (hm g (by simp)) _ _ h)

lemma eval_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply run_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, hi]

lemma impossible {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) (hx : f x = true) (hy : f y = false) :
    ¬ ∃ C : Circuit, Monotone2 C ∧ ∀ z : Fin n → Bool, C.eval (List.ofFn z) = f z := by
  rintro ⟨C, hm, hf⟩
  have h := eval_mono C hm x y hxy
  rw [hf, hf, hx, hy] at h
  exact Bool.false_ne_true (h rfl)

lemma wires_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  apply run_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp)
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, hi]


lemma wire_monotone (C : Circuit) (n w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    Monotone (fun x : Fin n → Bool => PEqualNP.BlindGate.wireValue C n x w) := by
  have hm : Monotone2 C := fun g hg => ⟨hC.1 g hg, (hC.2.2 g hg).le⟩
  intro x y hxy
  have hi : ∀ i,x i = true → y i = true := by
    intro i he
    exact Bool.le_iff_imp.mp (hxy i) he
  have he := wires_mono C hm x y hi w
  change (C.wires (List.ofFn x)).getD w false ≤ (C.wires (List.ofFn y)).getD w false
  exact Bool.le_iff_imp.mpr he

lemma eval_list_monotone (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (h : List.Forall₂ (· ≤ ·) x y) : C.eval x ≤ C.eval y := by
  have hi : ∀ i,x.getD i false ≤ y.getD i false := by
    induction h with
    | nil => intro i; simp
    | @cons a b xs ys hab h ih =>
      intro i
      cases i with
      | zero => simpa using hab
      | succ i => simpa using ih i
  have he := run_mono C.gates (fun g hg => (hm g hg).1) x y h.length_eq
    (fun i hh => Bool.le_iff_imp.mp (hi i) hh) C.output
  change (run C.gates x).getD C.output false ≤ (run C.gates y).getD C.output false
  exact Bool.le_iff_imp.mpr he


lemma monotone (n : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  exact Bool.le_iff_imp.mpr (eval_mono C hm x y (fun i => Bool.le_iff_imp.mp (hxy i)))
end PEqualNP.Outside.L_meta_19006.Helpers


theorem PEqualNP.Outside.L_meta_19006 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1 → Bool), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x6 : Fin x1), x3 x6 = Bool.true → x4 x6 = Bool.true) → x2.eval (List.ofFn x3) = Bool.true → x2.eval (List.ofFn x4) = Bool.true) := by
  intro n C x y hm h
  exact PEqualNP.Outside.L_meta_19006.Helpers.eval_mono C hm x y h
