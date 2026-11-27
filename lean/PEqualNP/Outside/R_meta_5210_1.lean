import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5210_1
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let v := PEqualNP.EdgeOwnership.gateVal 26 C
      let w := PEqualNP.CleanedNonEdge.wireVal 26 C
      let r := PEqualNP.EdgeOwnership.InCone 26 C
      PEqualNP.TopForm.IsAO2 26 C →
      ∀ p q e : Fin 26 → Bool,
      (∀ u, e u = true → p u = true ∨ q u = true) →
      C.eval (List.ofFn e) = true →
      C.eval (List.ofFn p) = false →
      C.eval (List.ofFn q) = false →
      ∀ i j : Nat,
      (i < C.size ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ v i e = true ∧
        ∀ a ∈ (g i).inputs, w a p = false) →
      (j < C.size ∧ (g j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ v j e = true ∧
        ∀ a ∈ (g j).inputs, w a q = false) →
      ¬ r i j → ¬ r j i →
      ∃ a < C.size, (g a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        v a e = true ∧ a ≠ i ∧ a ≠ j)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      let d : Finset (Fin 13) := {0, 1, 3, 9}
      let t : Nat → Prop := fun k => k < C.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.gateVal 26 C k
          (PEqualNP.EdgeOwnership.pairInput (0 : Fin 26) 13) = true
      PEqualNP.TopForm.IsAO2 26 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 13, u - v ∈ d ∧
          x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true) →
      (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ t i ∧ t j ∧ t k) →
      65 ≤ C.size) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
      have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;
      have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
      have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
      have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) =>
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧
        ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧
        x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)),
          PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;
      x1.size ≤ (64 : ℕ) ∧
      (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 →
        (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧
          x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧
      (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔
        ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧
          x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧
          x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧
      (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧
        ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧
      ∃ (x10 : ℕ) (x11 : ℕ), x10 ≠ x11 ∧ ¬x4 x10 x11 ∧ ¬x4 x11 x10 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  classical
  rintro ⟨C, hC⟩
  dsimp only at hC
  rcases hC with ⟨hsize, hshape, hfun, _, i, j, hij, hincij, hincji, hi, hj⟩
  let p : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 0 0
  let q : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 13 13
  let e : Fin 26 → Bool := PEqualNP.EdgeOwnership.pairInput 0 13
  have gat : ∀ k g, C.gates[k]? = some g →
      PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
    intro k g hg
    change C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g
    rw [List.getD_eq_getElem?_getD, hg]
    rfl
  have hc : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
      exact (hshape k g hk).1
    · intro k hk w hw
      have hg := List.getElem?_eq_getElem hk
      obtain ⟨_, u, v, hins, _, hu, hv⟩ := hshape k C.gates[k] hg
      rw [gat k C.gates[k] hg, hins] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨_, u, v, hins, _⟩ := hshape k g hk
      simp [hins]
  have hn : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨_, u, v, hins, huv, _⟩ := hshape k g hk
    simp [hins, huv]
  have bounds : ∀ k, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
      PEqualNP.CircuitLowerBounds.GateOp.and → k < C.size := by
    intro k ha
    by_contra hk
    change ¬ k < C.gates.length at hk
    have hz : PEqualNP.MetaComplexity.NestedCover.gateAt C k =
        ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
      exact List.getD_eq_default _ _ (by change C.gates.length ≤ k; omega)
    rw [hz] at ha
    cases ha
  have hcover : ∀ u, e u = true → p u = true ∨ q u = true := by
    intro u hu
    change decide (u = 0 ∨ u = 13) = true at hu
    change decide (u = 0 ∨ u = 0) = true ∨ decide (u = 13 ∨ u = 13) = true
    simpa only [or_self, decide_eq_true_eq] using hu
  have he : C.eval (List.ofFn e) = true := by
    exact (hfun e).mpr ⟨0, 0, by decide, by decide, by decide⟩
  have hp : C.eval (List.ofFn p) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨u, v, _, _, hv⟩ := (hfun p).mp ht
    change decide (Fin.natAdd 13 v = (0 : Fin 26) ∨ Fin.natAdd 13 v = 0) = true at hv
    have hzero : Fin.natAdd 13 v = (0 : Fin 26) :=
      (of_decide_eq_true hv).elim id id
    have hval := congrArg Fin.val hzero
    change 13 + v.val = 0 at hval
    omega
  have hq : C.eval (List.ofFn q) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨u, v, _, hu, _⟩ := (hfun q).mp ht
    change decide (Fin.castAdd 13 u = (13 : Fin 26) ∨ Fin.castAdd 13 u = 13) = true at hu
    have hthirteen : Fin.castAdd 13 u = (13 : Fin 26) :=
      (of_decide_eq_true hu).elim id id
    have hval := congrArg Fin.val hthirteen
    change u.val = 13 at hval
    have := u.isLt
    omega
  have lower : ∀ k x, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
      PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ b : Fin 2, PEqualNP.CleanedNonEdge.wireVal 26 C (PEqualNP.TopForm.opnd C k b) x = false) →
      ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs,
        PEqualNP.CleanedNonEdge.wireVal 26 C w x = false := by
    intro k x ha hf w hw
    have hk : k < C.gates.length := bounds k ha
    have hg := List.getElem?_eq_getElem hk
    obtain ⟨_, u, v, hins, _⟩ := hshape k C.gates[k] hg
    have hh := gat k C.gates[k] hg
    rw [hh, hins] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have hf0 := hf (0 : Fin 2)
      change PEqualNP.CleanedNonEdge.wireVal 26 C
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0) x = false at hf0
      rw [hh, hins] at hf0
      exact hf0
    · have hf1 := hf (1 : Fin 2)
      change PEqualNP.CleanedNonEdge.wireVal 26 C
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0) x = false at hf1
      rw [hh, hins] at hf1
      exact hf1
  obtain ⟨k, hk, hka, hke, hki, hkj⟩ := h1 C hc p q e hcover he hp hq i j
    ⟨bounds i hi.1, hi.1, hi.2.2.1, lower i p hi.1 hi.2.2.2⟩
    ⟨bounds j hj.1, hj.1, hj.2.2.1, lower j q hj.1 hj.2.2.2⟩ hincij hincji
  have hbound := h2 C hc hn hfun
    ⟨i, j, k, hij, Ne.symm hki, Ne.symm hkj,
      ⟨bounds i hi.1, hi.1, hi.2.2.1⟩,
      ⟨bounds j hj.1, hj.1, hj.2.2.1⟩, ⟨hk, hka, hke⟩⟩
  omega
