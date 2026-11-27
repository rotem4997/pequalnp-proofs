import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18920_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem foldl_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ i, w1.getD i false ≤ w2.getD i false) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w1).getD i false ≤
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w2).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ hle i; exact hle i
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hAO g (List.mem_cons_self ..)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hAO g' (List.mem_cons_of_mem g hg')
    have hstep : g.op.eval (g.inputs.map fun k => w1.getD k false) ≤
                 g.op.eval (g.inputs.map fun k => w2.getD k false) := by
      rcases hg with hop | hop <;> rw [hop]
      · simp only [GateOp.eval]
        cases h1 : (g.inputs.map fun k => w1.getD k false).all id
        · exact Bool.false_le _
        · have h2 : (g.inputs.map fun k => w2.getD k false).all id = true := by
            rw [List.all_eq_true] at h1 ⊢
            intro b hb
            rcases List.mem_map.mp hb with ⟨k, hk, rfl⟩
            have h1k := h1 (w1.getD k false) (List.mem_map.mpr ⟨k, hk, rfl⟩)
            have hle_k := hle k
            simp only [id] at h1k ⊢
            rw [h1k] at hle_k
            exact Bool.eq_true_of_true_le hle_k
          rw [h2]
      · simp only [GateOp.eval]
        cases h1 : (g.inputs.map fun k => w1.getD k false).any id
        · exact Bool.false_le _
        · have h2 : (g.inputs.map fun k => w2.getD k false).any id = true := by
            rw [List.any_eq_true] at h1 ⊢
            rcases h1 with ⟨b, hb, hbtrue⟩
            rcases List.mem_map.mp hb with ⟨k, hk, rfl⟩
            refine ⟨w2.getD k false, List.mem_map.mpr ⟨k, hk, rfl⟩, ?_⟩
            have hle_k := hle k
            simp only [id] at hbtrue ⊢
            rw [hbtrue] at hle_k
            exact Bool.eq_true_of_true_le hle_k
          rw [h2]
    apply ih hgs
    · simp [hlen]
    · intro i
      by_cases hi : i < w1.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
        exact hle i
      · by_cases heq : i = w1.length
        · subst heq
          have h1 : (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).getD w1.length false =
              g.op.eval (g.inputs.map fun k => w1.getD k false) := by simp [List.getD_eq_getElem?_getD]
          have h2 : (w2 ++ [g.op.eval (g.inputs.map fun k => w2.getD k false)]).getD w1.length false =
              g.op.eval (g.inputs.map fun k => w2.getD k false) := by rw [hlen]; simp [List.getD_eq_getElem?_getD]
          rw [h1, h2]
          exact hstep
        · have hge1 : (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).length ≤ i := by simp; omega
          have hge2 : (w2 ++ [g.op.eval (g.inputs.map fun k => w2.getD k false)]).length ≤ i := by simp [← hlen]; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

theorem main_proof :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      Monotone (PEqualNP.MetaComplexity.circuitFun 27 C) := by
  intro C hm x y hxy
  apply foldl_mono C.gates (fun g hg => (hm g hg).1) (List.ofFn x) (List.ofFn y) (by simp)
  intro i
  by_cases hi : i < 27
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
    exact hxy ⟨i, hi⟩
  · have h1 : (List.ofFn x).length ≤ i := by simp; omega
    have h2 : (List.ofFn y).length ≤ i := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none h1, List.getElem?_eq_none h2]

end PEqualNP.Outside.L_meta_18920_aux

theorem PEqualNP.Outside.L_meta_18920 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → Monotone (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x1))  := by
  exact PEqualNP.Outside.L_meta_18920_aux.main_proof
