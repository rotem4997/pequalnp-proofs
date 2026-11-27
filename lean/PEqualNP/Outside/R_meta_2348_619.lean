import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_2348_619
    (hSame :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Bool → ℕ → Bool) (j : ℕ),
        let op := PEqualNP.TopForm.opnd C
        let ga := PEqualNP.MetaComplexity.NestedCover.gateAt C
        let W : Bool → List Bool := fun s => C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
        (∀ k < C.size, op k 0 ≠ op k 1) → (ga 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        (∀ s : Bool,
          (∀ i < 14, v s i = decide (i = if s then 7 else 0)) ∧
          (∀ k < C.size,
            ((ga k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              v s (14 + k) = (((W s).getD (op k 0) false && v s (op k 1)) || (v s (op k 0) && (W s).getD (op k 1) false))) ∧
            ((ga k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
              v s (14 + k) = (v s (op k 0) || v s (op k 1)))) ∧
          v s C.output = false) →
        0 < j ∧ j < C.size ∧ (ga j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ t : Fin 2, 14 ≤ op j t) →
        (∀ s : Bool, ∀ t : Fin 2, (W s).getD (op j t) false = false ∧ v s (op j t) = true) →
        False)
    (hDiffBare :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Bool → ℕ → Bool) (jT jF : ℕ),
        let op := PEqualNP.TopForm.opnd C
        let ga := PEqualNP.MetaComplexity.NestedCover.gateAt C
        let W : Bool → List Bool := fun s => C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
        (∀ k < C.size, op k 0 ≠ op k 1) → (ga 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        (∀ s : Bool,
          (∀ i < 14, v s i = decide (i = if s then 7 else 0)) ∧
          (∀ k < C.size,
            ((ga k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              v s (14 + k) = (((W s).getD (op k 0) false && v s (op k 1)) || (v s (op k 0) && (W s).getD (op k 1) false))) ∧
            ((ga k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
              v s (14 + k) = (v s (op k 0) || v s (op k 1)))) ∧
          v s C.output = false) →
        0 < jT ∧ jT < jF ∧ jF < C.size →
        (∃ t : Fin 2, op jT t = 7) →
        (∀ s : Bool, let j := if s then jT else jF
          (ga j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∀ t : Fin 2, (W s).getD (op j t) false = false ∧ v s (op j t) = true) →
        False)
    (hDiffGate :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Bool → ℕ → Bool) (jT jF : ℕ),
        let op := PEqualNP.TopForm.opnd C
        let ga := PEqualNP.MetaComplexity.NestedCover.gateAt C
        let W : Bool → List Bool := fun s => C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
        (∀ k < C.size, op k 0 ≠ op k 1) → (ga 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        (∀ s : Bool,
          (∀ i < 14, v s i = decide (i = if s then 7 else 0)) ∧
          (∀ k < C.size,
            ((ga k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              v s (14 + k) = (((W s).getD (op k 0) false && v s (op k 1)) || (v s (op k 0) && (W s).getD (op k 1) false))) ∧
            ((ga k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
              v s (14 + k) = (v s (op k 0) || v s (op k 1)))) ∧
          v s C.output = false) →
        0 < jT ∧ jT < jF ∧ jF < C.size →
        (∀ t : Fin 2, 14 ≤ op jT t) →
        (∀ s : Bool, let j := if s then jT else jF
          (ga j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∀ t : Fin 2, (W s).getD (op j t) false = false ∧ v s (op j t) = true) →
        False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  classical
  intro C hSz hAO2 hDist hFirst hFun hTraces
  have andEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval xs = xs.any id := fun _ => rfl
  let run : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_snoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
    intro gs g x
    change (gs ++ [g]).foldl _ x = _
    rw [List.foldl_append]; rfl
  have hrun_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool),
      (run gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => rw [hrun_snoc]; simp [ih]; omega
  have hgetD_lt : ∀ {α : Type} (l : List α) (b d : α) (t : ℕ), t < l.length →
      (l ++ [b]).getD t d = l.getD t d := by
    intro α l b d t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD]
  have hgetD_at : ∀ {α : Type} (l : List α) (b d : α), (l ++ [b]).getD l.length d = b := by
    intro α l b d; simp [List.getD_eq_getElem?_getD]
  have hrun_prefix : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length + gs.length → (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
    intro gs hs x i hi
    induction hs using List.reverseRecOn with
    | nil => rw [List.append_nil]
    | append_singleton hs g ih =>
      rw [← List.append_assoc, hrun_snoc, hgetD_lt _ _ _ _ (by rw [hrun_len, List.length_append]; omega), ih]
  have hrun_input : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (i : ℕ),
      i < x.length → (run gs x).getD i false = x.getD i false := by
    intro gs x i hi
    have h1 := hrun_prefix [] gs x i (by rw [List.length_nil, Nat.add_zero]; exact hi)
    rw [List.nil_append] at h1; exact h1
  have hrun_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs x).getD (x.length + j) false =
        (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op.eval
          ((gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map fun i =>
            if i < x.length + j then (run gs x).getD i false else false) := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => intro j hj; exfalso; exact Nat.not_lt_zero j hj
    | append_singleton gs g ih =>
      intro j hj
      have hlen : (run gs x).length = x.length + gs.length := hrun_len gs x
      have hsame : ∀ k ≤ gs.length, ∀ l : List ℕ,
          (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
          l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
        intro k hk l
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · exact hrun_prefix gs [g] x i (by omega)
        · rfl
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · have hgd : (gs ++ [g]).getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
            gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
        rw [hgd, hsame j (Nat.le_of_lt hlt), hrun_prefix gs [g] x _ (by omega)]
        exact ih j hlt
      · have hjeq : j = gs.length := by rw [List.length_append, List.length_singleton] at hj; omega
        subst hjeq
        have hgd : (gs ++ [g]).getD gs.length ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [hgd, hsame gs.length le_rfl, hrun_snoc, ← hlen, hgetD_at]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        split_ifs with hlt
        · rfl
        · exact List.getD_eq_default _ _ (by omega)
  have hGateInfo : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 14 D →
      ∀ j < D.size,
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
         (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs =
          [PEqualNP.TopForm.opnd D j 0, PEqualNP.TopForm.opnd D j 1] ∧
        PEqualNP.TopForm.opnd D j 0 < 14 + j ∧ PEqualNP.TopForm.opnd D j 1 < 14 + j := by
    intro D hD j hj
    have hjg : j < D.gates.length := hj
    have hmem : PEqualNP.MetaComplexity.NestedCover.gateAt D j ∈ D.gates := by
      change D.gates.getD j _ ∈ D.gates
      rw [List.getD_eq_getElem _ _ hjg]
      exact List.getElem_mem hjg
    have hop := hD.1 _ hmem
    have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    have hin : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs =
        [PEqualNP.TopForm.opnd D j 0, PEqualNP.TopForm.opnd D j 1] := by
      rcases hgl : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs with _ | ⟨u, _ | ⟨v, _ | ⟨z, rest⟩⟩⟩
      · rw [hgl] at hlen; cases hlen
      · rw [hgl] at hlen; cases hlen
      · unfold PEqualNP.TopForm.opnd; rw [hgl]; rfl
      · rw [hgl] at hlen; cases hlen
    have hlt0 : PEqualNP.TopForm.opnd D j 0 < 14 + j := hD.2.1 j hjg _ (by rw [hin]; simp)
    have hlt1 : PEqualNP.TopForm.opnd D j 1 < 14 + j := hD.2.1 j hjg _ (by rw [hin]; simp)
    exact ⟨hop, hin, hlt0, hlt1⟩
  have hwires_in : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 14 → Bool) (w : ℕ) (hw : w < 14),
      (D.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro D x w hw
    change (run D.gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [hrun_input D.gates (List.ofFn x) w (by simp [hw])]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hw]
    rfl
  have hwires_gate : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 14 D →
      ∀ (x : Fin 14 → Bool) (j : ℕ) (hj : j < D.size),
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (D.wires (List.ofFn x)).getD (14 + j) false =
            ((D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 0) false &&
             (D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 1) false)) ∧
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          (D.wires (List.ofFn x)).getD (14 + j) false =
            ((D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 0) false ||
             (D.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd D j 1) false)) := by
    intro D hD x j hj
    obtain ⟨_, hin, hlt0, hlt1⟩ := hGateInfo D hD j hj
    have hrg := hrun_gate D.gates (List.ofFn x) j hj
    rw [List.length_ofFn] at hrg
    change (D.wires (List.ofFn x)).getD (14 + j) false =
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op.eval
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs.map fun i =>
          if i < 14 + j then (D.wires (List.ofFn x)).getD i false else false) at hrg
    rw [hin, List.map_cons, List.map_cons, List.map_nil, ite_eq_left hlt0, ite_eq_left hlt1] at hrg
    constructor
    · intro hop; rw [hrg, hop, andEval]; simp
    · intro hop; rw [hrg, hop, orEval]; simp
  let x01 : Fin 14 → Bool := fun i => decide (i = 0 ∨ i = 7)
  let baseIn : Bool → Fin 14 → Bool := fun s i => decide (i = if s then 0 else 7)
  have hFindWitness : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (v : Bool → ℕ → Bool),
      PEqualNP.TopForm.IsAO2 14 D →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool,
        let W := D.wires (List.ofFn (baseIn s))
        (∀ i < 14, v s i = decide (i = if s then 7 else 0)) ∧
        (∀ k < D.size,
          let g := PEqualNP.MetaComplexity.NestedCover.gateAt D k
          let a := PEqualNP.TopForm.opnd D k 0
          let b := PEqualNP.TopForm.opnd D k 1
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            v s (14 + k) = ((W.getD a false && v s b) || (v s a && W.getD b false))) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            v s (14 + k) = (v s a || v s b))) ∧
        v s D.output = false) →
      (14 ≤ D.output ∧ D.output < 14 + D.size) ∧
      ∀ s : Bool, ∃ j : ℕ, 0 < j ∧ j < D.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (∀ t : Fin 2,
          (D.wires (List.ofFn (baseIn s))).getD (PEqualNP.TopForm.opnd D j t) false = false ∧
          v s (PEqualNP.TopForm.opnd D j t) = true) := by
    intro D v hD hD0 hDfun hDv
    have hEval01 : D.eval (List.ofFn x01) = true :=
      (hDfun x01).mpr ⟨0, 0, Or.inl rfl, by decide, by decide⟩
    have hOutLt : D.output < 14 + D.size := by
      by_contra hge
      have hlen : (D.wires (List.ofFn x01)).length = 14 + D.size := by
        change (run D.gates (List.ofFn x01)).length = 14 + D.gates.length
        rw [hrun_len, List.length_ofFn]
      have hdef : (D.wires (List.ofFn x01)).getD D.output false = false :=
        List.getD_eq_default _ _ (by omega)
      change (D.wires (List.ofFn x01)).getD D.output false = true at hEval01
      rw [hdef] at hEval01; cases hEval01
    have hOutGe : 14 ≤ D.output := by
      by_contra hlt
      have hlt' : D.output < 14 := Nat.lt_of_not_ge hlt
      let xs : Fin 14 → Bool := fun i => decide (i.val = D.output)
      have hev : D.eval (List.ofFn xs) = true := by
        change (D.wires (List.ofFn xs)).getD D.output false = true
        rw [hwires_in D xs D.output hlt']
        simp [xs]
      obtain ⟨u, t, _, hu, ht⟩ := (hDfun xs).mp hev
      simp [xs] at hu ht
      omega
    refine ⟨⟨hOutGe, hOutLt⟩, fun s => ?_⟩
    obtain ⟨hvIn, hvGate, hvOut⟩ := hDv s
    let U := D.wires (List.ofFn x01)
    let W := D.wires (List.ofFn (baseIn s))
    have hEvalBase : W.getD D.output false = false := by
      cases hwb : W.getD D.output false
      · rfl
      · exfalso
        obtain ⟨u, t, _, hu, ht⟩ := (hDfun (baseIn s)).mp hwb
        dsimp only [baseIn] at hu ht
        rw [decide_eq_true_eq] at hu ht
        have hu' : (Fin.castAdd 7 u).val < 7 := u.isLt
        have ht' : 7 ≤ (Fin.natAdd 7 t).val := by simp
        cases s
        · have h1 := congrArg Fin.val hu; simp at h1; omega
        · have h1 := congrArg Fin.val ht; simp at h1
    let Bad (j : ℕ) : Prop :=
      j < D.size ∧ U.getD (14 + j) false = true ∧ W.getD (14 + j) false = false ∧ v s (14 + j) = false
    have hExBad : ∃ j, Bad j := by
      by_contra hNoBad
      have hAll : ∀ w < 14 + D.size, U.getD w false = true → W.getD w false = true ∨ v s w = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw hUw
          by_cases hw14 : w < 14
          · rw [hwires_in D x01 w hw14] at hUw
            rw [hwires_in D (baseIn s) w hw14, hvIn w hw14]
            dsimp only [x01, baseIn] at hUw ⊢
            rw [decide_eq_true_eq] at hUw
            rcases hUw with h0 | h7
            · have hweq : w = 0 := congrArg Fin.val h0
              cases s
              · right; simp [hweq]
              · left; rw [h0]; decide
            · have hweq : w = 7 := congrArg Fin.val h7
              cases s
              · left; rw [h7]; decide
              · right; simp [hweq]
          · let k : ℕ := w - 14
            have hwk : w = 14 + k := by omega
            have hkD : k < D.size := by omega
            rw [hwk] at hUw ⊢
            by_contra hBothF
            apply hNoBad
            refine ⟨k, hkD, hUw, ?_, ?_⟩
            · cases hw' : W.getD (14 + k) false
              · rfl
              · exact False.elim (hBothF (Or.inl hw'))
            · cases hv' : v s (14 + k)
              · rfl
              · exact False.elim (hBothF (Or.inr hv'))
      have hOutTrue : U.getD D.output false = true := hEval01
      rcases hAll D.output hOutLt hOutTrue with hW | hV
      · rw [hEvalBase] at hW; cases hW
      · rw [hvOut] at hV; cases hV
    let j := Nat.find hExBad
    have hjBad : Bad j := Nat.find_spec hExBad
    have hjMin : ∀ k < j, ¬ Bad k := fun k hk => Nat.find_min hExBad hk
    have hCov : ∀ w < 14 + j, U.getD w false = true → W.getD w false = true ∨ v s w = true := by
      intro w hw hUw
      by_cases hw14 : w < 14
      · rw [hwires_in D x01 w hw14] at hUw
        rw [hwires_in D (baseIn s) w hw14, hvIn w hw14]
        dsimp only [x01, baseIn] at hUw ⊢
        rw [decide_eq_true_eq] at hUw
        rcases hUw with h0 | h7
        · have hweq : w = 0 := congrArg Fin.val h0
          cases s
          · right; simp [hweq]
          · left; rw [h0]; decide
        · have hweq : w = 7 := congrArg Fin.val h7
          cases s
          · left; rw [h7]; decide
          · right; simp [hweq]
      · let k : ℕ := w - 14
        have hwk : w = 14 + k := by omega
        rw [hwk] at hUw ⊢
        by_contra hBothF
        apply hjMin k (by omega)
        refine ⟨by omega, hUw, ?_, ?_⟩
        · cases hw' : W.getD (14 + k) false
          · rfl
          · exact False.elim (hBothF (Or.inl hw'))
        · cases hv' : v s (14 + k)
          · rfl
          · exact False.elim (hBothF (Or.inr hv'))
    obtain ⟨hjD, hUj, hWj, hVj⟩ := hjBad
    obtain ⟨hjOp, _, hlt0, hlt1⟩ := hGateInfo D hD j hjD
    have hjAnd : (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases hjOp with hand | hor
      · exact hand
      · exfalso
        have hUor := (hwires_gate D hD x01 j hjD).2 hor
        have hWor := (hwires_gate D hD (baseIn s) j hjD).2 hor
        have hVor := (hvGate j hjD).2 hor
        change U.getD (14 + j) false = (U.getD (PEqualNP.TopForm.opnd D j 0) false || U.getD (PEqualNP.TopForm.opnd D j 1) false) at hUor
        change W.getD (14 + j) false = (W.getD (PEqualNP.TopForm.opnd D j 0) false || W.getD (PEqualNP.TopForm.opnd D j 1) false) at hWor
        rw [hUj] at hUor
        rw [hWj] at hWor
        rw [hVj] at hVor
        have hW0 : W.getD (PEqualNP.TopForm.opnd D j 0) false = false := (Bool.or_eq_false_iff.mp hWor.symm).1
        have hW1 : W.getD (PEqualNP.TopForm.opnd D j 1) false = false := (Bool.or_eq_false_iff.mp hWor.symm).2
        have hV0 : v s (PEqualNP.TopForm.opnd D j 0) = false := (Bool.or_eq_false_iff.mp hVor.symm).1
        have hV1 : v s (PEqualNP.TopForm.opnd D j 1) = false := (Bool.or_eq_false_iff.mp hVor.symm).2
        rcases Bool.or_eq_true_iff.mp hUor.symm with hU0 | hU1
        · rcases hCov _ hlt0 hU0 with h | h
          · rw [hW0] at h; cases h
          · rw [hV0] at h; cases h
        · rcases hCov _ hlt1 hU1 with h | h
          · rw [hW1] at h; cases h
          · rw [hV1] at h; cases h
    have hjPos : 0 < j := by
      by_contra hz
      have hj0 : j = 0 := by omega
      rw [hj0, hD0] at hjAnd; cases hjAnd
    have hUand := (hwires_gate D hD x01 j hjD).1 hjAnd
    have hWand := (hwires_gate D hD (baseIn s) j hjD).1 hjAnd
    have hVand := (hvGate j hjD).1 hjAnd
    change U.getD (14 + j) false = (U.getD (PEqualNP.TopForm.opnd D j 0) false && U.getD (PEqualNP.TopForm.opnd D j 1) false) at hUand
    change W.getD (14 + j) false = (W.getD (PEqualNP.TopForm.opnd D j 0) false && W.getD (PEqualNP.TopForm.opnd D j 1) false) at hWand
    rw [hUj] at hUand
    rw [hWj] at hWand
    rw [hVj] at hVand
    have hU0 : U.getD (PEqualNP.TopForm.opnd D j 0) false = true := (Bool.and_eq_true_iff.mp hUand.symm).1
    have hU1 : U.getD (PEqualNP.TopForm.opnd D j 1) false = true := (Bool.and_eq_true_iff.mp hUand.symm).2
    have hC0 := hCov _ hlt0 hU0
    have hC1 := hCov _ hlt1 hU1
    have hW0 : W.getD (PEqualNP.TopForm.opnd D j 0) false = false := by
      cases h0 : W.getD (PEqualNP.TopForm.opnd D j 0) false
      · rfl
      · exfalso
        cases h1 : W.getD (PEqualNP.TopForm.opnd D j 1) false
        · rcases hC1 with h1' | hv1
          · rw [h1] at h1'; cases h1'
          · rw [h0, hv1] at hVand; simp at hVand
        · rw [h0, h1] at hWand; simp at hWand
    have hW1 : W.getD (PEqualNP.TopForm.opnd D j 1) false = false := by
      cases h1 : W.getD (PEqualNP.TopForm.opnd D j 1) false
      · rfl
      · exfalso
        rcases hC0 with h0' | hv0
        · rw [hW0] at h0'; cases h0'
        · rw [h1, hv0] at hVand; simp at hVand
    have hV0 : v s (PEqualNP.TopForm.opnd D j 0) = true := by
      rcases hC0 with h0' | hv0
      · rw [hW0] at h0'; cases h0'
      · exact hv0
    have hV1 : v s (PEqualNP.TopForm.opnd D j 1) = true := by
      rcases hC1 with h1' | hv1
      · rw [hW1] at h1'; cases h1'
      · exact hv1
    refine ⟨j, hjPos, hjD, hjAnd, fun t => ?_⟩
    fin_cases t
    · exact ⟨hW0, hV0⟩
    · exact ⟨hW1, hV1⟩
  have hDispatch : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (v : Bool → ℕ → Bool) (jT jF : ℕ),
      D.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 D →
      (∀ k < D.size, PEqualNP.TopForm.opnd D k 0 ≠ PEqualNP.TopForm.opnd D k 1) →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      14 ≤ D.output → D.output < 14 + D.size →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool,
        let W := D.wires (List.ofFn (baseIn s))
        (∀ i < 14, v s i = decide (i = if s then 7 else 0)) ∧
        (∀ k < D.size,
          let g := PEqualNP.MetaComplexity.NestedCover.gateAt D k
          let a := PEqualNP.TopForm.opnd D k 0
          let b := PEqualNP.TopForm.opnd D k 1
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            v s (14 + k) = ((W.getD a false && v s b) || (v s a && W.getD b false))) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            v s (14 + k) = (v s a || v s b))) ∧
        v s D.output = false) →
      0 < jT → jT ≤ jF → jF < D.size →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D jT).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt D jF).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (∀ s : Bool, let j := if s then jT else jF
        ∀ t : Fin 2,
          (D.wires (List.ofFn (baseIn s))).getD (PEqualNP.TopForm.opnd D j t) false = false ∧
          v s (PEqualNP.TopForm.opnd D j t) = true) →
      False := by
    intro D v jT jF hDsz hDao hDdist hD0 hDoutGe hDoutLt hDfun hDv hjTpos hjLe hjFlt hjTand hjFand hBoth
    by_cases heq : jT = jF
    · subst heq
      have hGe14 : ∀ t : Fin 2, 14 ≤ PEqualNP.TopForm.opnd D jT t := by
        intro t
        by_contra hlt
        have hlt14 : PEqualNP.TopForm.opnd D jT t < 14 := Nat.lt_of_not_ge hlt
        have hvt : v true (PEqualNP.TopForm.opnd D jT t) = true := (hBoth true t).2
        have hvf : v false (PEqualNP.TopForm.opnd D jT t) = true := (hBoth false t).2
        rw [(hDv true).1 _ hlt14] at hvt
        rw [(hDv false).1 _ hlt14] at hvf
        simp at hvt hvf
        omega
      exact hSame D v jT hDsz hDao hDdist hD0 hDfun hDv ⟨hjTpos, hjFlt, hjTand⟩ hGe14
        (fun s t => by cases s <;> exact hBoth _ t)
    · have hjLt : jT < jF := lt_of_le_of_ne hjLe heq
      have hBoth' : ∀ s : Bool, let j := if s then jT else jF
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∀ t : Fin 2,
            (D.wires (List.ofFn (baseIn s))).getD (PEqualNP.TopForm.opnd D j t) false = false ∧
            v s (PEqualNP.TopForm.opnd D j t) = true := by
        intro s
        cases s
        · exact ⟨hjFand, hBoth false⟩
        · exact ⟨hjTand, hBoth true⟩
      by_cases hBare : ∃ t : Fin 2, PEqualNP.TopForm.opnd D jT t = 7
      · exact hDiffBare D v jT jF hDsz hDao hDdist hD0 hDfun hDv ⟨hjTpos, hjLt, hjFlt⟩ hBare hBoth'
      · have hGe14 : ∀ t : Fin 2, 14 ≤ PEqualNP.TopForm.opnd D jT t := by
          intro t
          by_contra hlt
          have hlt14 : PEqualNP.TopForm.opnd D jT t < 14 := Nat.lt_of_not_ge hlt
          have hvt : v true (PEqualNP.TopForm.opnd D jT t) = true := (hBoth true t).2
          rw [(hDv true).1 _ hlt14] at hvt
          simp at hvt
          exact hBare ⟨t, hvt⟩
        exact hDiffGate D v jT jF hDsz hDao hDdist hD0 hDfun hDv ⟨hjTpos, hjLt, hjFlt⟩ hGe14 hBoth'
  choose v hv using hTraces
  obtain ⟨⟨hCoutGe, hCoutLt⟩, hWit⟩ := hFindWitness C v hAO2 hFirst hFun hv
  obtain ⟨jT, hjTpos, hjTlt, hjTand, hjTw⟩ := hWit true
  obtain ⟨jF, hjFpos, hjFlt, hjFand, hjFw⟩ := hWit false
  by_cases hOrder : jT ≤ jF
  · exact hDispatch C v jT jF hSz hAO2 hDist hFirst hCoutGe hCoutLt hFun hv hjTpos hOrder hjFlt hjTand hjFand
      (fun s t => by cases s; exact hjFw t; exact hjTw t)
  · let swapArr : Fin 14 → Fin 14 := ![7, 13, 12, 11, 10, 9, 8, 0, 6, 5, 4, 3, 2, 1]
    have hSwapInvol : ∀ i : Fin 14, swapArr (swapArr i) = i := by decide +kernel
    have hSwap0 : swapArr 0 = 7 := by decide
    have hSwap7 : swapArr 7 = 0 := by decide
    let adjFano (i j : Fin 14) : Bool :=
      let p := min i.val j.val
      let l := max i.val j.val - 7
      decide (p < 7 ∧ 7 ≤ max i.val j.val ∧ (p = l ∨ p = (l + 1) % 7 ∨ p = (l + 3) % 7))
    have hEdgeIff : ∀ i j : Fin 14,
        (∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          ((i = Fin.castAdd 7 u ∧ j = Fin.natAdd 7 t) ∨ (j = Fin.castAdd 7 u ∧ i = Fin.natAdd 7 t))) ↔
        adjFano i j = true := by
      dsimp only [adjFano]; decide +kernel
    have hSwapAdj : ∀ i j : Fin 14, adjFano (swapArr i) (swapArr j) = adjFano i j := by
      dsimp only [adjFano, swapArr]; decide +kernel
    let M (w : ℕ) : ℕ := if h : w < 14 then (swapArr ⟨w, h⟩).val else w
    have hMlt : ∀ w : ℕ, M w < 14 ↔ w < 14 := by
      intro w
      by_cases hw : w < 14
      · simp only [M, dite_eq_left hw, hw, iff_true]; exact (swapArr ⟨w, hw⟩).isLt
      · simp [M, hw]
    have hMfin : ∀ i : Fin 14, M i.val = (swapArr i).val := fun i => by simp [M, i.isLt]
    have hMinv : ∀ w : ℕ, M (M w) = w := by
      intro w
      by_cases hw : w < 14
      · let i : Fin 14 := ⟨w, hw⟩
        change M (M i.val) = i.val
        rw [hMfin, hMfin, hSwapInvol]
      · simp [M, hw]
    have hMbound : ∀ w k : ℕ, w < 14 + k → M w < 14 + k := by
      intro w k hwk
      by_cases hw : w < 14
      · have := (hMlt w).2 hw; omega
      · simpa [M, hw] using hwk
    let mapGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
      ⟨g.op, g.inputs.map M⟩
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map mapGate, M C.output⟩
    have hDsize : D.size = C.size := List.length_map mapGate
    have hDgate : ∀ k < C.size,
        PEqualNP.MetaComplexity.NestedCover.gateAt D k =
          mapGate (PEqualNP.MetaComplexity.NestedCover.gateAt C k) := by
      intro k hk
      change (C.gates.map mapGate).getD k _ = mapGate (C.gates.getD k _)
      rw [List.getD_eq_getElem _ _ (by simp; exact hk),
          List.getD_eq_getElem _ _ hk, List.getElem_map]
      rfl
    have hDinputs : ∀ k < C.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs =
          [M (PEqualNP.TopForm.opnd C k 0), M (PEqualNP.TopForm.opnd C k 1)] := by
      intro k hk
      rw [hDgate k hk]
      change (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.map M = _
      rw [(hGateInfo C hAO2 k hk).2.1]
      rfl
    have hDopnd : ∀ k < C.size,
        PEqualNP.TopForm.opnd D k 0 = M (PEqualNP.TopForm.opnd C k 0) ∧
        PEqualNP.TopForm.opnd D k 1 = M (PEqualNP.TopForm.opnd C k 1) := by
      intro k hk
      change (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs.getD 0 0 = _ ∧
             (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs.getD 1 0 = _
      rw [hDinputs k hk]
      exact ⟨rfl, rfl⟩
    have hDao : PEqualNP.TopForm.IsAO2 14 D := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hAO2.1 g' hg'
      · intro k hk w hw
        have hk' : k < C.size := hDsize ▸ hk
        rw [hDinputs k hk', List.mem_cons, List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl
        · exact hMbound _ k (hGateInfo C hAO2 k hk').2.2.1
        · exact hMbound _ k (hGateInfo C hAO2 k hk').2.2.2
      · intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        change (g'.inputs.map M).length = 2
        rw [List.length_map]
        exact hAO2.2.2 g' hg'
    have hDdist : ∀ k < D.size, PEqualNP.TopForm.opnd D k 0 ≠ PEqualNP.TopForm.opnd D k 1 := by
      intro k hk
      have hk' : k < C.size := hDsize ▸ hk
      rw [(hDopnd k hk').1, (hDopnd k hk').2]
      intro heq
      have h1 := congrArg M heq
      rw [hMinv, hMinv] at h1
      exact hDist k hk' h1
    have hD0 : (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      rw [hDgate 0 (by omega)]
      exact hFirst
    have hDout : D.output = C.output := by
      change M C.output = C.output
      simp [M, show ¬ C.output < 14 by omega]
    have hDwires : ∀ (x : Fin 14 → Bool) (w : ℕ), w < 14 + C.size →
        (D.wires (List.ofFn x)).getD (M w) false = (C.wires (List.ofFn (x ∘ swapArr))).getD w false := by
      intro x w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hwlt
        by_cases hw14 : w < 14
        · let i : Fin 14 := ⟨w, hw14⟩
          change (D.wires (List.ofFn x)).getD (M i.val) false = (C.wires (List.ofFn (x ∘ swapArr))).getD i.val false
          rw [hMfin, hwires_in D x (swapArr i).val (swapArr i).isLt, hwires_in C (x ∘ swapArr) i.val i.isLt]
          rfl
        · let k : ℕ := w - 14
          have hwk : w = 14 + k := by omega
          have hkC : k < C.size := by omega
          have hkD : k < D.size := hDsize.symm ▸ hkC
          have hMw : M w = 14 + k := by simp [M, hwk]
          rw [hMw, hwk]
          have hOpEq : (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op =
              (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op := by rw [hDgate k hkC]
          obtain ⟨hCop, _, hlt0, hlt1⟩ := hGateInfo C hAO2 k hkC
          rcases hCop with hand | hor
          · rw [(hwires_gate D hDao x k hkD).1 (hOpEq.trans hand),
                (hwires_gate C hAO2 (x ∘ swapArr) k hkC).1 hand,
                (hDopnd k hkC).1, (hDopnd k hkC).2,
                ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
          · rw [(hwires_gate D hDao x k hkD).2 (hOpEq.trans hor),
                (hwires_gate C hAO2 (x ∘ swapArr) k hkC).2 hor,
                (hDopnd k hkC).1, (hDopnd k hkC).2,
                ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
    have hDfun : ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
      intro x
      have hEv : D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ swapArr)) := by
        change (D.wires (List.ofFn x)).getD (M C.output) false =
          (C.wires (List.ofFn (x ∘ swapArr))).getD C.output false
        exact hDwires x C.output hCoutLt
      rw [hEv, hFun]
      have halt : ∀ y : Fin 14 → Bool,
          (∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            y (Fin.castAdd 7 u) = true ∧ y (Fin.natAdd 7 t) = true) ↔
          ∃ i j : Fin 14, adjFano i j = true ∧ y i = true ∧ y j = true := by
        intro y
        constructor
        · rintro ⟨u, t, h, hu, ht⟩
          exact ⟨Fin.castAdd 7 u, Fin.natAdd 7 t, (hEdgeIff _ _).mp ⟨u, t, h, Or.inl ⟨rfl, rfl⟩⟩, hu, ht⟩
        · rintro ⟨i, j, hij, hi, hj⟩
          obtain ⟨u, t, h, he⟩ := (hEdgeIff i j).mpr hij
          rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨u, t, h, hi, hj⟩
          · exact ⟨u, t, h, hj, hi⟩
      rw [halt (x ∘ swapArr), halt x]
      constructor
      · rintro ⟨i, j, hij, hi, hj⟩
        exact ⟨swapArr i, swapArr j, (hSwapAdj i j).trans hij, hi, hj⟩
      · rintro ⟨i, j, hij, hi, hj⟩
        refine ⟨swapArr i, swapArr j, (hSwapAdj i j).trans hij, ?_, ?_⟩
        · change x (swapArr (swapArr i)) = true; rwa [hSwapInvol]
        · change x (swapArr (swapArr j)) = true; rwa [hSwapInvol]
    let v' : Bool → ℕ → Bool := fun s w => v (!s) (M w)
    have hBaseSwap : ∀ s : Bool, baseIn s ∘ swapArr = baseIn (!s) := by
      intro s
      funext i
      dsimp only [Function.comp_apply, baseIn]
      apply Bool.decide_congr
      cases s
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
        constructor
        · intro h; have := congrArg swapArr h; rwa [hSwapInvol, hSwap7] at this
        · intro h; rw [h, hSwap0]
      · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
        constructor
        · intro h; have := congrArg swapArr h; rwa [hSwapInvol, hSwap0] at this
        · intro h; rw [h, hSwap7]
    have hDv' : ∀ s : Bool,
        let W := D.wires (List.ofFn (baseIn s))
        (∀ i < 14, v' s i = decide (i = if s then 7 else 0)) ∧
        (∀ k < D.size,
          let g := PEqualNP.MetaComplexity.NestedCover.gateAt D k
          let a := PEqualNP.TopForm.opnd D k 0
          let b := PEqualNP.TopForm.opnd D k 1
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            v' s (14 + k) = ((W.getD a false && v' s b) || (v' s a && W.getD b false))) ∧
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            v' s (14 + k) = (v' s a || v' s b))) ∧
        v' s D.output = false := by
      intro s
      obtain ⟨hIn, hG, hO⟩ := hv (!s)
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        change v (!s) (M i) = decide (i = if s then 7 else 0)
        rw [hIn (M i) ((hMlt i).2 hi)]
        apply Bool.decide_congr
        let fi : Fin 14 := ⟨i, hi⟩
        have hMfi : M i = (swapArr fi).val := hMfin fi
        rw [hMfi]
        cases s
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          constructor
          · intro h
            have h1 : swapArr fi = 7 := Fin.ext h
            have h2 := congrArg swapArr h1
            rw [hSwapInvol, hSwap7] at h2
            exact congrArg Fin.val h2
          · intro h
            have h1 : fi = 0 := Fin.ext h
            rw [h1, hSwap0]; rfl
        · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
          constructor
          · intro h
            have h1 : swapArr fi = 0 := Fin.ext h
            have h2 := congrArg swapArr h1
            rw [hSwapInvol, hSwap0] at h2
            exact congrArg Fin.val h2
          · intro h
            have h1 : fi = 7 := Fin.ext h
            rw [h1, hSwap7]; rfl
      · intro k hk
        have hkC : k < C.size := hDsize ▸ hk
        have hOpEq : (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op =
            (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op := by rw [hDgate k hkC]
        have hM14 : M (14 + k) = 14 + k := by simp [M, show ¬ 14 + k < 14 by omega]
        have hlt0 := (hGateInfo C hAO2 k hkC).2.2.1
        have hlt1 := (hGateInfo C hAO2 k hkC).2.2.2
        have hW0 : (D.wires (List.ofFn (baseIn s))).getD (PEqualNP.TopForm.opnd D k 0) false =
            (C.wires (List.ofFn (baseIn (!s)))).getD (PEqualNP.TopForm.opnd C k 0) false := by
          rw [(hDopnd k hkC).1, hDwires (baseIn s) _ (by omega), hBaseSwap s]
        have hW1 : (D.wires (List.ofFn (baseIn s))).getD (PEqualNP.TopForm.opnd D k 1) false =
            (C.wires (List.ofFn (baseIn (!s)))).getD (PEqualNP.TopForm.opnd C k 1) false := by
          rw [(hDopnd k hkC).2, hDwires (baseIn s) _ (by omega), hBaseSwap s]
        have hV0 : v' s (PEqualNP.TopForm.opnd D k 0) = v (!s) (PEqualNP.TopForm.opnd C k 0) := by
          change v (!s) (M (PEqualNP.TopForm.opnd D k 0)) = _
          rw [(hDopnd k hkC).1, hMinv]
        have hV1 : v' s (PEqualNP.TopForm.opnd D k 1) = v (!s) (PEqualNP.TopForm.opnd C k 1) := by
          change v (!s) (M (PEqualNP.TopForm.opnd D k 1)) = _
          rw [(hDopnd k hkC).2, hMinv]
        have hGk := hG k hkC
        constructor
        · intro hand
          change v (!s) (M (14 + k)) = _
          rw [hM14, hW0, hW1, hV0, hV1]
          exact hGk.1 (hOpEq ▸ hand)
        · intro hor
          change v (!s) (M (14 + k)) = _
          rw [hM14, hV0, hV1]
          exact hGk.2 (hOpEq ▸ hor)
      · change v (!s) (M (M C.output)) = false
        rw [hMinv]
        exact hO
    refine hDispatch D v' jF jT (by omega) hDao hDdist hD0 (by omega) (by omega) hDfun hDv' hjFpos (by omega) (by omega)
      (by rw [hDgate jF hjFlt]; exact hjFand) (by rw [hDgate jT hjTlt]; exact hjTand) ?_
    intro s
    dsimp only
    intro t
    cases s
    · change (D.wires (List.ofFn (baseIn false))).getD (PEqualNP.TopForm.opnd D jT t) false = false ∧
        v' false (PEqualNP.TopForm.opnd D jT t) = true
      have hlt : PEqualNP.TopForm.opnd C jT t < 14 + jT := by
        fin_cases t; exact (hGateInfo C hAO2 jT hjTlt).2.2.1; exact (hGateInfo C hAO2 jT hjTlt).2.2.2
      have hop : PEqualNP.TopForm.opnd D jT t = M (PEqualNP.TopForm.opnd C jT t) := by
        fin_cases t; exact (hDopnd jT hjTlt).1; exact (hDopnd jT hjTlt).2
      rw [hop, hDwires (baseIn false) _ (by omega), hBaseSwap false]
      change (C.wires (List.ofFn (baseIn true))).getD (PEqualNP.TopForm.opnd C jT t) false = false ∧
        v true (M (M (PEqualNP.TopForm.opnd C jT t))) = true
      rw [hMinv]
      exact hjTw t
    · change (D.wires (List.ofFn (baseIn true))).getD (PEqualNP.TopForm.opnd D jF t) false = false ∧
        v' true (PEqualNP.TopForm.opnd D jF t) = true
      have hlt : PEqualNP.TopForm.opnd C jF t < 14 + jF := by
        fin_cases t; exact (hGateInfo C hAO2 jF hjFlt).2.2.1; exact (hGateInfo C hAO2 jF hjFlt).2.2.2
      have hop : PEqualNP.TopForm.opnd D jF t = M (PEqualNP.TopForm.opnd C jF t) := by
        fin_cases t; exact (hDopnd jF hjFlt).1; exact (hDopnd jF hjFlt).2
      rw [hop, hDwires (baseIn true) _ (by omega), hBaseSwap true]
      change (C.wires (List.ofFn (baseIn false))).getD (PEqualNP.TopForm.opnd C jF t) false = false ∧
        v false (M (M (PEqualNP.TopForm.opnd C jF t))) = true
      rw [hMinv]
      exact hjFw t
