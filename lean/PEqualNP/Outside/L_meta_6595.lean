import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6595

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepGate x := rfl

lemma foldl_stepGate_len (gs : List Gate) (init : List Bool) :
    (gs.foldl stepGate init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g tl ih => simp [List.foldl, stepGate, ih]; omega

lemma foldl_stepGate_getD_prefix (gs : List Gate) (init : List Bool) (i : ℕ)
    (hi : i < init.length) :
    (gs.foldl stepGate init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.foldl]
    have hlen : i < (stepGate init g).length := by simp [stepGate]; omega
    rw [ih (stepGate init g) hlen]
    simp [stepGate, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_stepGate_getD_prefix C.gates x i hi

lemma wires_getD_oob (C : Circuit) (x : List Bool) (w : ℕ) (hw : x.length + C.gates.length ≤ w) :
    (C.wires x).getD w false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_eq_foldl, foldl_stepGate_len]; omega)]; rfl

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hj] at this
    exact this.symm
  conv_lhs => rw [wires_eq_foldl, hsplit, List.foldl_append, List.foldl_cons]
  set pref := (C.gates.take j).foldl stepGate x
  have hplen : pref.length = x.length + j := by
    rw [foldl_stepGate_len, List.length_take, Nat.min_eq_left (by omega)]
  have hstep_len : x.length + j < (stepGate pref C.gates[j]).length := by
    simp [stepGate, hplen]
  rw [foldl_stepGate_getD_prefix _ (stepGate pref C.gates[j]) (x.length + j) hstep_len]
  have hget : (stepGate pref C.gates[j]).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => pref.getD i false) := by
    simp [stepGate, List.getD_eq_getElem?_getD, hplen]
  rw [hget]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · simp only [hi, ite_true]
    have hpi : i < pref.length := by omega
    have h1 := foldl_stepGate_getD_prefix (C.gates[j] :: C.gates.drop (j + 1)) pref i hpi
    rw [← h1]
    simp only [wires_eq_foldl]
    conv_rhs => rw [hsplit, List.foldl_append]
  · simp only [hi, ite_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

lemma main (x1 x2 : ℕ) (x3 : Circuit) (hAO : IsAO2 x1 x3)
    (x5 : Fin x2 × Fin x2 → Fin x1 → Bool)
    (x6 : Finset (Fin x2) → Fin x1 → Bool) :
    ∃ (x7 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2))),
      (∀ (x8 : ℕ), ∃ (x9 : Set (Fin x2 × Fin x2)) (x10 : Set (Finset (Fin x2))), x7 x8 = x9 ×ˢ x10) ∧
      (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x2 × Fin x2) × Finset (Fin x2) | x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false}) ∧
      (∀ (x8 : Fin x3.size), ∃ x9 < x1 + ↑x8, ∃ x10 < x1 + ↑x8, (x3.gates.get x8).inputs = [x9, x10] ∧ x7 (x1 + ↑x8) ⊆ x7 x9 ∪ x7 x10) ∧
      (x3.output < x1 + x3.size ∨ x7 x3.output = ∅) ∧
      x7 x3.output = {x8 : (Fin x2 × Fin x2) × Finset (Fin x2) | circuitFun x1 x3 (x5 x8.1) = Bool.true ∧ circuitFun x1 x3 (x6 x8.2) = Bool.false} := by
  let wval (w : ℕ) (y : Fin x1 → Bool) : Bool := (x3.wires (List.ofFn y)).getD w false
  let x7 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2)) :=
    fun w => { p | wval w (x5 p.1) = true ∧ wval w (x6 p.2) = false }
  refine ⟨x7, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    refine ⟨{ a | wval w (x5 a) = true }, { b | wval w (x6 b) = false }, rfl⟩
  · intro i
    ext p
    simp only [x7, wval, Set.mem_setOf_eq]
    have hlen1 : (List.ofFn (x5 p.1)).length = x1 := List.length_ofFn
    have hlen2 : (List.ofFn (x6 p.2)).length = x1 := List.length_ofFn
    rw [wires_getD_input x3 _ i.val (by omega), wires_getD_input x3 _ i.val (by omega)]
    simp [List.getD_eq_getElem?_getD, i.isLt]
  · intro j
    have hj : j.val < x3.gates.length := j.isLt
    have hmem : x3.gates[j.val] ∈ x3.gates := List.getElem_mem hj
    have hlen2 : (x3.gates[j.val]).inputs.length = 2 := hAO.2.2 _ hmem
    have hop : (x3.gates[j.val]).op = .and ∨ (x3.gates[j.val]).op = .or := hAO.1 _ hmem
    have hrb : ∀ u ∈ (x3.gates[j.val]).inputs, u < x1 + j.val := by
      intro u hu
      have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt x3 j.val = x3.gates[j.val] := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        simp [List.getD_eq_getElem?_getD, hj]
      exact hAO.2.1 j.val hj u (by rw [hgat]; exact hu)
    rcases List.length_eq_two.mp hlen2 with ⟨a, b, hab⟩
    have ha : a < x1 + j.val := hrb a (by rw [hab]; simp)
    have hb : b < x1 + j.val := hrb b (by rw [hab]; simp)
    refine ⟨a, ha, b, hb, ?_, ?_⟩
    · exact hab
    · intro p hp
      simp only [x7, wval, Set.mem_setOf_eq, Set.mem_union] at hp ⊢
      rcases hop with hand | hor
      · have hev : ∀ y : Fin x1 → Bool,
            (x3.wires (List.ofFn y)).getD (x1 + j.val) false =
              ((x3.wires (List.ofFn y)).getD a false && (x3.wires (List.ofFn y)).getD b false) := by
          intro y
          have hly : (List.ofFn y).length = x1 := List.length_ofFn
          have hgate := wires_getD_gate x3 (List.ofFn y) j.val hj
          rw [hly] at hgate
          rw [hgate, hab, hand]
          simp [GateOp.eval, ha, hb]
        rw [hev (x5 p.1), hev (x6 p.2)] at hp
        simp only [Bool.and_eq_true, Bool.and_eq_false_iff] at hp
        rcases hp.2 with hf | hf
        · exact Or.inl ⟨hp.1.1, hf⟩
        · exact Or.inr ⟨hp.1.2, hf⟩
      · have hev : ∀ y : Fin x1 → Bool,
            (x3.wires (List.ofFn y)).getD (x1 + j.val) false =
              ((x3.wires (List.ofFn y)).getD a false || (x3.wires (List.ofFn y)).getD b false) := by
          intro y
          have hly : (List.ofFn y).length = x1 := List.length_ofFn
          have hgate := wires_getD_gate x3 (List.ofFn y) j.val hj
          rw [hly] at hgate
          rw [hgate, hab, hor]
          simp [GateOp.eval, ha, hb]
        rw [hev (x5 p.1), hev (x6 p.2)] at hp
        simp only [Bool.or_eq_true, Bool.or_eq_false_iff] at hp
        rcases hp.1 with ht | ht
        · exact Or.inl ⟨ht, hp.2.1⟩
        · exact Or.inr ⟨ht, hp.2.2⟩
  · by_cases hout : x3.output < x1 + x3.size
    · exact Or.inl hout
    · right
      ext p
      simp only [x7, wval, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1
      have h0 := wires_getD_oob x3 (List.ofFn (x5 p.1)) x3.output (by rw [List.length_ofFn]; exact Nat.not_lt.mp hout)
      rw [h0] at h1
      cases h1
  · rfl

end PEqualNP.Outside.L_meta_6595

theorem PEqualNP.Outside.L_meta_6595 :
    ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x3 → ∀ (x5 : Fin x2 × Fin x2 → Fin x1 → Bool) (x6 : Finset (Fin x2) → Fin x1 → Bool), ∃ (x7 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2))), (∀ (x8 : ℕ), ∃ (x9 : Set (Fin x2 × Fin x2)) (x10 : Set (Finset (Fin x2))), x7 x8 = x9 ×ˢ x10) ∧ (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x2 × Fin x2) × Finset (Fin x2) | x5 x9.1 x8 = Bool.true ∧ x6 x9.2 x8 = Bool.false}) ∧ (∀ (x8 : Fin x3.size), ∃ x9 < x1 + ↑x8, ∃ x10 < x1 + ↑x8, (x3.gates.get x8).inputs = [x9, x10] ∧ x7 (x1 + ↑x8) ⊆ x7 x9 ∪ x7 x10) ∧ (x3.output < x1 + x3.size ∨ x7 x3.output = ∅) ∧ x7 x3.output = {x8 : (Fin x2 × Fin x2) × Finset (Fin x2) | PEqualNP.MetaComplexity.circuitFun x1 x3 (x5 x8.1) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 (x6 x8.2) = Bool.false} :=
  PEqualNP.Outside.L_meta_6595.main
