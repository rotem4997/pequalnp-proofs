import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_18765.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wires_prefix (gs : List Gate) (x : List Bool) :
    ∃ t : List Bool, run gs x = x ++ t ∧ t.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t,ht,hl⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: t, ?_, by simp [hl]⟩
    change run gs (x ++ [_]) = _
    rw [ht]
    simp

lemma length_run (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  obtain ⟨t,ht,hl⟩ := wires_prefix gs x
  simp [ht,hl]

lemma input_value (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  obtain ⟨t,ht,_⟩ := wires_prefix C.gates x
  change (run C.gates x).getD i false = _
  rw [ht,List.getD_append _ _ _ _ hi]

lemma append_eval (C : Circuit) (x : List Bool) (op : GateOp) (a b : ℕ) :
    ({ gates := C.gates ++ [{op := op, inputs := [a,b]}],
       output := x.length + C.size } : Circuit).eval x =
       op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
  have hl : (C.wires x).length = x.length + C.size := length_run C.gates x
  simp only [Circuit.eval,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change ((C.wires x) ++ [op.eval [(C.wires x).getD a false,(C.wires x).getD b false]]).getD
    (x.length+C.size) false = _
  rw [← hl]
  simp [Circuit.wires]

lemma append_monotone (C : Circuit) (hC : Monotone2 C) (op : GateOp)
    (hop : op = .and ∨ op = .or) (a b out : ℕ) :
    Monotone2 {gates := C.gates ++ [{op := op,inputs := [a,b]}],output := out} := by
  intro g hg
  simp only [List.mem_append,List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hC g hg
  · exact ⟨hop,by simp⟩

lemma append_size (C : Circuit) (g : Gate) (out : ℕ) :
    ({gates := C.gates ++ [g],output := out} : Circuit).size = C.size + 1 := by
  simp [Circuit.size]
lemma append_ao2 (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (op : GateOp) (hop : op = .and ∨ op = .or) (a b out : ℕ)
    (ha : a < n+C.size) (hb : b < n+C.size) :
    PEqualNP.TopForm.IsAO2 n {gates := C.gates ++ [{op := op,inputs := [a,b]}], output := out} := by
  refine ⟨?_,?_,?_⟩
  · intro g hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.1 g hg
    · exact hop
  · intro j hj i hi
    change j < (C.gates ++ [_]).length at hj
    change i ∈ ((C.gates ++ [_]).getD j {op := .or,inputs := []}).inputs at hi
    by_cases hj' : j < C.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hC.2.1 j hj' i hi
    · have heq : j = C.gates.length := by simp only [List.length_append,List.length_singleton] at hj; omega
      subst j
      simp only [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self,List.getD_cons_zero,
        List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [List.mem_append,List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.2.2 g hg
    · rfl

lemma append_nodup (C : Circuit) (hC : ∀ g ∈ C.gates,g.inputs.Nodup)
    (op : GateOp) (a b out : ℕ) (hab : a ≠ b) :
    ∀ g ∈ ({gates := C.gates ++ [{op := op,inputs := [a,b]}],output := out} : Circuit).gates,
      g.inputs.Nodup := by
  intro g hg
  simp only [List.mem_append,List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hC g hg
  · simpa using hab

def appendGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  {gates := C.gates ++ [{op := op,inputs := [a,b]}],output := n+C.size}

lemma wireValue_append (n : ℕ) (C : Circuit) (x : Fin n → Bool) (op : GateOp)
    (a b i : ℕ) (hi : i < n+C.size) :
    PEqualNP.BlindGate.wireValue (appendGate n C op a b) n x i =
      PEqualNP.BlindGate.wireValue C n x i := by
  have hl : (C.wires (List.ofFn x)).length = n+C.size := by
    simpa [Circuit.wires,Circuit.size,run] using length_run C.gates (List.ofFn x)
  simp only [PEqualNP.BlindGate.wireValue,appendGate,Circuit.wires,List.foldl_append,
    List.foldl_cons,List.foldl_nil]
  change ((C.wires (List.ofFn x)) ++ [_]).getD i false = _
  rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
  rfl

lemma wireValue_new (n : ℕ) (C : Circuit) (x : Fin n → Bool) (op : GateOp) (a b : ℕ) :
    PEqualNP.BlindGate.wireValue (appendGate n C op a b) n x (n+C.size) =
      op.eval [PEqualNP.BlindGate.wireValue C n x a,PEqualNP.BlindGate.wireValue C n x b] := by
  simpa [appendGate,List.length_ofFn,PEqualNP.BlindGate.wireValue,Circuit.eval] using
    append_eval C (List.ofFn x) op a b

lemma two_or_outputs (n : ℕ) (C : Circuit) (r s : ℕ) (t : Fin n)
    (hao : PEqualNP.TopForm.IsAO2 n C) (hnd : ∀ g ∈ C.gates,g.inputs.Nodup)
    (hr : r < n+C.size) (hs : s < n+C.size) (hrs : r ≠ s) (hrt : r ≠ t.val) :
    ∃ (D : Circuit) (a b : ℕ), D.size ≤ C.size+2 ∧ PEqualNP.TopForm.IsAO2 n D ∧
      (∀ g ∈ D.gates,g.inputs.Nodup) ∧ a ≠ b ∧ a < n+D.size ∧ b < n+D.size ∧
      ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue D n x a =
          (PEqualNP.BlindGate.wireValue C n x r || PEqualNP.BlindGate.wireValue C n x s) ∧
        PEqualNP.BlindGate.wireValue D n x b =
          (PEqualNP.BlindGate.wireValue C n x r || x t) := by
  let C1 := appendGate n C .or r s
  let D := appendGate n C1 .or r t.val
  have size1 : C1.size = C.size+1 := append_size C _ _
  have sizeD : D.size = C1.size+1 := append_size C1 _ _
  have hao1 : PEqualNP.TopForm.IsAO2 n C1 := append_ao2 n C hao .or (Or.inr rfl) r s _ hr hs
  have hnd1 : ∀ g ∈ C1.gates,g.inputs.Nodup := append_nodup C hnd .or r s _ hrs
  have hr1 : r < n+C1.size := by omega
  have ht1 : t.val < n+C1.size := by omega
  refine ⟨D,n+C.size,n+C1.size,by omega,?_,?_,by omega,by omega,by omega,?_⟩
  · exact append_ao2 n C1 hao1 .or (Or.inr rfl) r t.val _ hr1 ht1
  · exact append_nodup C1 hnd1 .or r t.val _ hrt
  · intro x
    have ht : PEqualNP.BlindGate.wireValue C1 n x t.val = x t := by
      unfold PEqualNP.BlindGate.wireValue
      rw [input_value C1 (List.ofFn x) t.val (by simp)]
      simp
    constructor
    · rw [show D = appendGate n C1 .or r t.val from rfl,
        wireValue_append n C1 x .or r t.val (n+C.size) (by omega)]
      simpa [C1,GateOp.eval] using wireValue_new n C x .or r s
    · rw [show D = appendGate n C1 .or r t.val from rfl,wireValue_new,ht]
      rw [show C1 = appendGate n C .or r s from rfl,wireValue_append n C x .or r s r hr]
      simp [GateOp.eval]
end PEqualNP.Outside.L_meta_18765.Helpers


theorem PEqualNP.Outside.L_meta_18765 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x7 ∈ x2.gates, x7.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → x3 ≠ ↑x5 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : ℕ) (x14 : ℕ), x12.size ≤ x2.size + (2 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x12 ∧ (∀ x15 ∈ x12.gates, x15.inputs.Nodup) ∧ x13 ≠ x14 ∧ x13 < x1 + x12.size ∧ x14 < x1 + x12.size ∧ ∀ (x15 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x12 x1 x15 x13 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || PEqualNP.BlindGate.wireValue x2 x1 x15 x4) ∧ PEqualNP.BlindGate.wireValue x12 x1 x15 x14 = (PEqualNP.BlindGate.wireValue x2 x1 x15 x3 || x15 x5)) := by
  exact PEqualNP.Outside.L_meta_18765.Helpers.two_or_outputs
