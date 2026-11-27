import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- All incident pairs in the Fano plane are equivalent under affine permutations.
-- A relabeling result transports the normalization to and from the pair (0, 0).
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4928_1
    (move : ∀ (C : Circuit) (n : ℕ) (σ : Equiv.Perm (Fin n)),
      let wire := fun w => if h : w < n then (σ ⟨w,h⟩).val else w
      ∃ D : Circuit, D.size = C.size ∧
        (∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
          ∃ h : Gate, C.gates[j]? = some h ∧ g.op = h.op ∧ g.inputs = h.inputs.map wire) ∧
        (D.output :: D.gates.flatMap Gate.inputs).filter (fun w => decide (n ≤ w)) =
          (C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (n ≤ w)) ∧
        (∀ i : Fin n, D.lineDeg n {(σ i).val} = C.lineDeg n {i.val}) ∧
        (SingleLevel.andDepths D n).getD D.output 0 = (SingleLevel.andDepths C n).getD C.output 0 ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)))
    (central : let inc := fun u t : Fin 7 => u = t ∨ u = t+1 ∨ u = t+3
      let valid := fun C : Circuit =>
        C.size ≤ 27 ∧
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = .and ∨ g.op = .or) ∧
          ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, inc u t ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true
      let tree := fun C : Circuit =>
        ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
      ∀ C : Circuit, valid C → 2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} →
        2 ≤ (SingleLevel.andDepths C 14).getD C.output 0 → ¬tree C →
        ∃ D : Circuit, valid D ∧ tree D ∧ 2 ≤ D.lineDeg 14 {0} ∧ 2 ≤ D.lineDeg 14 {7}) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ));
    have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧
      (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧
      ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true;
    have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup;
    ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)),
      x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x4 (14 : ℕ)).getD x4.output (0 : ℕ) →
      ¬x3 x4 →
      ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x2 x13 ∧ x3 x13 ∧ (2 : ℕ) ≤ x13.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x13.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  intro inc valid tree C p l correct edge degP degL depth shared
  have adjust : ∀ p l u t : Fin 7, inc p l →
      let a : Fin 7 := if p=l then 1 else if p=l+1 then 4 else 2
      inc (a * (u-p)) (a * (t-l)) ↔ inc u t := by
    dsimp only [inc]
    decide +kernel
  have affineBij : ∀ (a b : Fin 7), a ≠ 0 →
      Function.Bijective (fun x : Fin 7 => a * (x-b)) := by
    decide +kernel
  let a : Fin 7 := if p=l then 1 else if p=l+1 then 4 else 2
  have nz : a ≠ 0 := by
    dsimp [a]
    split <;> first | decide | split <;> decide
  let point := Equiv.ofBijective _ (affineBij a p nz)
  let line := Equiv.ofBijective _ (affineBij a l nz)
  have pzero : point p = 0 := by
    change a * (p-p) = 0
    rw [sub_self, mul_zero]
  have lzero : line l = 0 := by
    change a * (l-l) = 0
    rw [sub_self, mul_zero]
  have auto : ∀ u t, inc (point u) (line t) ↔ inc u t :=
    fun u t => adjust p l u t edge
  let blocks : Fin 7 ⊕ Fin 7 ≃ Fin 14 := finSumFinEquiv
  let labels : Equiv.Perm (Fin 14) := (blocks.symm.trans (Equiv.sumCongr point line)).trans blocks
  have points (u : Fin 7) : labels (Fin.castAdd 7 u) = Fin.castAdd 7 (point u) := by
    rw [← finSumFinEquiv_apply_left]
    change blocks ((Equiv.sumCongr point line) (blocks.symm (blocks (Sum.inl u)))) = _
    rw [blocks.symm_apply_apply]
    rfl
  have lines (t : Fin 7) : labels (Fin.natAdd 7 t) = Fin.natAdd 7 (line t) := by
    rw [← finSumFinEquiv_apply_right]
    change blocks ((Equiv.sumCongr point line) (blocks.symm (blocks (Sum.inr t)))) = _
    rw [blocks.symm_apply_apply]
    rfl
  have transport (B : Circuit) (α β : Equiv.Perm (Fin 7)) (σ : Equiv.Perm (Fin 14))
      (P : ∀ u : Fin 7, σ (Fin.castAdd 7 u) = Fin.castAdd 7 (α u))
      (L : ∀ t : Fin 7, σ (Fin.natAdd 7 t) = Fin.natAdd 7 (β t))
      (A : ∀ u t, inc (α u) (β t) ↔ inc u t) (ok : valid B) :
      ∃ D : Circuit, valid D ∧ (tree D ↔ tree B) ∧
        (∀ u : Fin 7, D.lineDeg 14 {(α u).val} = B.lineDeg 14 {u.val}) ∧
        (∀ t : Fin 7, D.lineDeg 14 {7+(β t).val} = B.lineDeg 14 {7+t.val}) ∧
        (SingleLevel.andDepths D 14).getD D.output 0 =
          (SingleLevel.andDepths B 14).getD B.output 0 := by
    let wire (w : ℕ) := if h : w < 14 then (σ ⟨w,h⟩).val else w
    obtain ⟨D, sz, gs, internal, deg, deep, ev⟩ := move B 14 σ
    have unique : Function.Injective wire := by
      intro i j eq
      by_cases hi : i < 14 <;> by_cases hj : j < 14
      · have q : σ ⟨i,hi⟩ = σ ⟨j,hj⟩ := Fin.ext (by simpa only [wire, dite_eq_left hi, dite_eq_left hj] using eq)
        exact congrArg Fin.val (σ.injective q)
      · have h := (σ ⟨i,hi⟩).isLt
        simp only [wire, dite_eq_left hi, dite_eq_right hj] at eq
        omega
      · have h := (σ ⟨j,hj⟩).isLt
        simp only [wire, dite_eq_right hi, dite_eq_left hj] at eq
        omega
      · simpa only [wire, dite_eq_right hi, dite_eq_right hj] using eq
    have earlier (j i : ℕ) (limit : i < 14+j) : wire i < 14+j := by
      unfold wire
      split
      · exact lt_of_lt_of_le (σ _).isLt (Nat.le_add_right _ _)
      · exact limit
    have dOK : valid D := by
      change D.size ≤ 27 ∧ _ ∧ _
      refine ⟨sz.trans_le ok.1, ?_, ?_⟩
      · intro j g found
        obtain ⟨h, hFound, hOp, hWires⟩ := gs j g found
        obtain ⟨gateOp, i, k, wires, diff, loI, loK⟩ := ok.2.1 j h hFound
        refine ⟨hOp ▸ gateOp, wire i, wire k, ?_, fun e => diff (unique e), earlier j i loI, earlier j k loK⟩
        rw [hWires, wires]
        rfl
      · intro x
        rw [ev, ok.2.2]
        constructor
        · rintro ⟨u,t,h,hu,ht⟩
          refine ⟨α u, β t, (A u t).2 h, ?_, ?_⟩
          · simpa only [Function.comp_apply, P] using hu
          · simpa only [Function.comp_apply, L] using ht
        · rintro ⟨u,t,h,hu,ht⟩
          obtain ⟨u,rfl⟩ := α.surjective u
          obtain ⟨t,rfl⟩ := β.surjective t
          refine ⟨u,t,(A u t).1 h, ?_, ?_⟩
          · simpa only [Function.comp_apply, P] using hu
          · simpa only [Function.comp_apply, L] using ht
    refine ⟨D, dOK, ?_, ?_, ?_, deep⟩
    · change ((D.output :: D.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup ↔
        ((B.output :: B.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
      rw [internal]
    · intro u
      have h := deg (Fin.castAdd 7 u)
      rw [P u] at h
      exact h
    · intro t
      have h := deg (Fin.natAdd 7 t)
      rw [L t] at h
      exact h
  obtain ⟨translated, validT, treeT, dpt, dlt, depthT⟩ :=
    transport C point line labels points lines auto correct
  have left := dpt p
  have right := dlt l
  rw [pzero] at left
  rw [lzero] at right
  obtain ⟨formula, validF, treeF, leftF, rightF⟩ :=
    central translated validT (left.symm ▸ degP) (right.symm ▸ degL)
      (depthT.symm ▸ depth) (fun h => shared (treeT.mp h))
  have inverseP (u : Fin 7) :
      labels.symm (Fin.castAdd 7 u) = Fin.castAdd 7 (point.symm u) := by
    apply labels.injective
    rw [labels.apply_symm_apply, points, point.apply_symm_apply]
  have inverseL (t : Fin 7) :
      labels.symm (Fin.natAdd 7 t) = Fin.natAdd 7 (line.symm t) := by
    apply labels.injective
    rw [labels.apply_symm_apply, lines, line.apply_symm_apply]
  have inverseAuto (u t : Fin 7) : inc (point.symm u) (line.symm t) ↔ inc u t := by
    simpa only [Equiv.apply_symm_apply] using (auto (point.symm u) (line.symm t)).symm
  obtain ⟨D, validD, treeD, lD, rD, _⟩ :=
    transport formula point.symm line.symm labels.symm inverseP inverseL inverseAuto validF
  have leftD := lD 0
  have rightD := rD 0
  have pointBack : point.symm 0 = p :=
    point.injective ((point.apply_symm_apply 0).trans pzero.symm)
  have lineBack : line.symm 0 = l :=
    line.injective ((line.apply_symm_apply 0).trans lzero.symm)
  rw [pointBack] at leftD
  rw [lineBack] at rightD
  exact ⟨D, validD, treeD.mpr treeF, leftD.symm ▸ leftF, rightD.symm ▸ rightF⟩
