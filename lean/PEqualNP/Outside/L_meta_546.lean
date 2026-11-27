import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_546_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

lemma run_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ hi

def shiftIdx (n : ℕ) (i : ℕ) : ℕ :=
  if i < n then i else i + 2

def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftIdx n)⟩

lemma run_shift (n : ℕ) (gs : List Gate) (w₁ w₂ : List Bool)
    (h1 : n ≤ w₁.length) (h2 : w₂.length = w₁.length + 2)
    (hagree : ∀ i, w₂.getD (shiftIdx n i) false = w₁.getD i false) :
    ∀ i, (run (gs.map (shiftGate n)) w₂).getD (shiftIdx n i) false =
      (run gs w₁).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hagree
  | cons g gs ih =>
    simp only [List.map_cons]
    change ∀ i, (run (gs.map (shiftGate n)) (step w₂ (shiftGate n g))).getD (shiftIdx n i) false =
      (run gs (step w₁ g)).getD i false
    apply ih (step w₁ g) (step w₂ (shiftGate n g))
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      have heval : (shiftGate n g).op.eval ((shiftGate n g).inputs.map fun j => w₂.getD j false) =
          g.op.eval (g.inputs.map fun j => w₁.getD j false) := by
        simp only [shiftGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact hagree j
      by_cases hlt : i < w₁.length
      · have hlt' : shiftIdx n i < w₂.length := by
          unfold shiftIdx
          split_ifs <;> omega
        rw [step, step, getD_snoc_lt _ _ _ hlt', getD_snoc_lt _ _ _ hlt]
        exact hagree i
      · by_cases heq : i = w₁.length
        · subst heq
          have hsh : shiftIdx n w₁.length = w₂.length := by
            unfold shiftIdx
            rw [if_neg (by omega)]
            omega
          rw [hsh, step, step, getD_snoc_eq, getD_snoc_eq, heval]
        · have hge1 : (step w₁ g).length ≤ i := by simp [step]; omega
          have hge2 : (step w₂ (shiftGate n g)).length ≤ shiftIdx n i := by
            unfold shiftIdx
            split_ifs <;> simp [step] <;> omega
          rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]

end PEqualNP.Outside.L_meta_546_aux

theorem PEqualNP.Outside.L_meta_546 :
    ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool) (v : Fin n),
      PEqualNP.MetaComplexity.HasCircuitSize n g s →
      PEqualNP.MetaComplexity.HasCircuitSize (n + 2)
        (fun x : Fin (n + 2) → Bool =>
          g (fun i : Fin n => x (Fin.castAdd 2 i)) ||
            (x (Fin.natAdd n 0) && (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1))))
        (s + 3) := by
  intro n s g v ⟨C, hfan, hsize, heval⟩
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_546_aux in
  let m := C.gates.length
  let outWire := if C.output < n + m then shiftIdx n C.output else n + 2 + m + 3
  let g1 : Gate := ⟨GateOp.or, [v.val, n + 1]⟩
  let g2 : Gate := ⟨GateOp.and, [n, n + 2 + m]⟩
  let g3 : Gate := ⟨GateOp.or, [outWire, n + 2 + m + 1]⟩
  let C' : Circuit := ⟨C.gates.map (shiftGate n) ++ [g1, g2, g3], n + 2 + m + 2⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro gate hgate
    simp only [C', List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hgate
    rcases hgate with ⟨g0, hg0, rfl⟩ | rfl | rfl | rfl
    · obtain ⟨hop, hlen⟩ := hfan g0 hg0
      exact ⟨hop, by simpa [shiftGate] using hlen⟩
    · exact ⟨by simp [g1], by simp [g1]⟩
    · exact ⟨by simp [g2], by simp [g2]⟩
    · exact ⟨by simp [g3], by simp [g3]⟩
  · change C'.gates.length ≤ s + 3
    change C.gates.length ≤ s at hsize
    simp only [C', List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  · intro x
    let y : Fin n → Bool := fun i => x (Fin.castAdd 2 i)
    have hbase : ∀ i, (List.ofFn x).getD (shiftIdx n i) false = (List.ofFn y).getD i false := by
      intro i
      by_cases hi : i < n
      · unfold shiftIdx
        rw [if_pos hi, getD_ofFn x i (by omega), getD_ofFn y i hi]
        rfl
      · unfold shiftIdx
        rw [if_neg hi]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hshift := run_shift n C.gates (List.ofFn y) (List.ofFn x) (by simp) (by simp) hbase
    set W0 := run (C.gates.map (shiftGate n)) (List.ofFn x)
    have hW0_len : W0.length = n + 2 + m := by
      simp [W0, run_length, m]
    have hW0_lt : ∀ k (hk : k < n + 2), W0.getD k false = x ⟨k, hk⟩ := by
      intro k hk
      rw [show W0 = run (C.gates.map (shiftGate n)) (List.ofFn x) from rfl,
        run_getD_of_lt _ _ k (by simp [List.length_ofFn]; omega), getD_ofFn x k hk]
    have hW0_out : W0.getD outWire false = g y := by
      rw [← heval y]
      change W0.getD outWire false = (run C.gates (List.ofFn y)).getD C.output false
      by_cases ho : C.output < n + m
      · have hout : outWire = shiftIdx n C.output := by simp [outWire, ho]
        rw [hout]
        exact hshift C.output
      · have hout : outWire = n + 2 + m + 3 := by simp [outWire, ho]
        rw [hout]
        rw [List.getD_eq_default _ _ (by rw [hW0_len]; omega),
          List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)]
    set W1 := step W0 g1
    set W2 := step W1 g2
    set W3 := step W2 g3
    have hW1_val : W1.getD (n + 2 + m) false = (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1)) := by
      rw [← hW0_len]
      simp only [W1, step, getD_snoc_eq, g1, GateOp.eval, List.map_cons, List.map_nil]
      rw [hW0_lt v.val (by omega), hW0_lt (n + 1) (by omega)]
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
      rfl
    have hW1_len : W1.length = n + 2 + m + 1 := by simp [W1, step, hW0_len]
    have hW2_val : W2.getD (n + 2 + m + 1) false =
        (x (Fin.natAdd n 0) && (x (Fin.castAdd 2 v) || x (Fin.natAdd n 1))) := by
      rw [← hW1_len]
      simp only [W2, step, getD_snoc_eq, g2, GateOp.eval, List.map_cons, List.map_nil]
      rw [show W1.getD n false = W0.getD n false from getD_snoc_lt _ _ _ (by omega),
        hW0_lt n (by omega), hW1_val]
      simp [Fin.natAdd]
    have hW2_len : W2.length = n + 2 + m + 2 := by simp [W2, step, hW1_len]
    have hW2_out : W2.getD outWire false = g y := by
      by_cases ho : C.output < n + m
      · have hout_lt : outWire < W0.length := by
          simp only [outWire, if_pos ho, shiftIdx]
          rw [hW0_len]
          split_ifs <;> omega
        rw [show W2.getD outWire false = W1.getD outWire false from
            getD_snoc_lt _ _ _ (by omega),
          show W1.getD outWire false = W0.getD outWire false from
            getD_snoc_lt _ _ _ hout_lt,
          hW0_out]
      · have hout : outWire = n + 2 + m + 3 := by simp [outWire, ho]
        rw [← hW0_out, hout,
          List.getD_eq_default W2 _ (by omega),
          List.getD_eq_default W0 _ (by omega)]
    have hW3_eq : C'.wires (List.ofFn x) = W3 := by
      change run (C.gates.map (shiftGate n) ++ [g1, g2, g3]) (List.ofFn x) = W3
      rw [run_append]
      rfl
    change (C'.wires (List.ofFn x)).getD (n + 2 + m + 2) false = _
    rw [hW3_eq, ← hW2_len]
    simp only [W3, step, getD_snoc_eq, g3, GateOp.eval, List.map_cons, List.map_nil]
    rw [hW2_out, hW2_val]
    simp [y]
