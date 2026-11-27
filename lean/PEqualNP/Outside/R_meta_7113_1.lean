import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_7113_1
 (hAnd : let R : List (List ℕ) := [[0,1],[0,2],[0,7],[0,8],[0,11],[1,2],[1,3],[1,8],[1,9],[1,11],[2,4],[2,6],[2,8],[2,10]]
 let W : List ℕ := [2111159234527359,4675347059835475,9350660026287268,13230028855838916,19181020142586886,27075955222729233,37332865189321860,45082562460688914,64214953892392450,16256]
 ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
 (∀ g ∈ C.gates, g.inputs.Nodup) →
 (∃ g, C.gates.head? = some g ∧ g.op = GateOp.and ∧ (g.inputs ∈ R ∨ g.inputs.reverse ∈ R)) →
 (∀ p l : Fin 7, p ∈ fanoLines l → C.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true) →
 (∀ k : Fin 37, C.eval (List.ofFn fun i : Fin 14 => (W.getD (k.val / 4) 0).testBit (14 * (k.val % 4) + i.val)) = false) →
 let V : ℕ → ℕ → Bool := fun m w => (C.wires (List.ofFn fun i : Fin 14 => m.testBit i.val)).getD w false
 ∀ j, (gateAt C j).op = GateOp.and → V 129 (14+j) = true →
 (∀ b : Fin 2, V 1 (opnd C j b) = false ∧ V 128 (opnd C j b) = false) → False)
 (hOr : let R : List (List ℕ) := [[0,1],[0,2],[0,7],[0,8],[0,11],[1,2],[1,3],[1,8],[1,9],[1,11],[2,4],[2,6],[2,8],[2,10]]
 let W : List ℕ := [2111159234527359,4675347059835475,9350660026287268,13230028855838916,19181020142586886,27075955222729233,37332865189321860,45082562460688914,64214953892392450,16256]
 ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
 (∀ g ∈ C.gates, g.inputs.Nodup) →
 (∃ g, C.gates.head? = some g ∧ g.op = GateOp.or ∧ (g.inputs ∈ R ∨ g.inputs.reverse ∈ R)) →
 (∀ p l : Fin 7, p ∈ fanoLines l → C.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true) →
 (∀ k : Fin 37, C.eval (List.ofFn fun i : Fin 14 => (W.getD (k.val / 4) 0).testBit (14 * (k.val % 4) + i.val)) = false) →
 let V : ℕ → ℕ → Bool := fun m w => (C.wires (List.ofFn fun i : Fin 14 => m.testBit i.val)).getD w false
 ∀ j, (gateAt C j).op = GateOp.and → V 129 (14+j) = true →
 (∀ b : Fin 2, V 1 (opnd C j b) = false ∧ V 128 (opnd C j b) = false) → False) :
 (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x5 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x6 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), x7 ∈ PEqualNP.CircuitLowerBounds.fanoLines x8 ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true)) → ¬(List.filter (fun (x7 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x7)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {(7 : ℕ)} → ∀ (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x10 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x10) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x14 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x10 x14) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x10 x14) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → False) := by
  classical
  have size_def (C : Circuit) : C.size = C.gates.length := rfl
  have wires_def (C : Circuit) (x : List Bool) : C.wires x =
      C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := rfl
  have eval_def (C : Circuit) (x : List Bool) : C.eval x = (C.wires x).getD C.output false := rfl
  have gateAt_def (C : Circuit) (j : Nat) : gateAt C j = C.gates.getD j ⟨GateOp.or,[]⟩ := rfl
  have opnd_def (C : Circuit) (j : Nat) (b : Fin 2) : opnd C j b = (gateAt C j).inputs.getD b.val 0 := rfl
  have gateVal_def (n : Nat) (C : Circuit) (j : Nat) (x : Fin n → Bool) :
      gateVal n C j x = (C.wires (List.ofFn x)).getD (n+j) false := rfl
  have pairInput_def {n : Nat} (u v : Fin n) : pairInput u v = (fun w => decide (w = u ∨ w = v)) := rfl


  let lift {n : ℕ} (p : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
    if h : w < n then (p ⟨w,h⟩).val else w

  let gate {n : ℕ} (p : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
    ⟨g.op,g.inputs.map (lift p)⟩

  let circuit {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
    ⟨C.gates.map (gate p), lift p C.output⟩

  have lift_input {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
      lift p i.val = (p i).val := by simp [lift, i.isLt]

  have lift_ge {n : ℕ} (p : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) :
      lift p w = w := by simp [lift, Nat.not_lt.mpr h]

  have lift_lt {n : ℕ} (p : Equiv.Perm (Fin n)) {m w : ℕ} (hm : n ≤ m) :
      lift p w < m ↔ w < m := by
    by_cases h : w < n
    · have hp : (p ⟨w,h⟩).val < n := (p ⟨w,h⟩).isLt
      simp only [lift, dite_eq_left h]
      omega
    · simp [lift, h]

  have lift_injective {n : ℕ} (p : Equiv.Perm (Fin n)) : Function.Injective (lift p) := by
    intro a b hab
    by_cases ha : a < n
    · by_cases hb : b < n
      · simp only [lift, dite_eq_left ha, dite_eq_left hb] at hab
        exact congrArg Fin.val (p.injective (Fin.ext hab))
      · have hp := (p ⟨a,ha⟩).isLt
        simp only [lift, dite_eq_left ha, dite_eq_right hb] at hab
        omega
    · by_cases hb : b < n
      · have hp := (p ⟨b,hb⟩).isLt
        simp only [lift, dite_eq_right ha, dite_eq_left hb] at hab
        omega
      · simpa [lift,ha,hb] using hab

  let run {α : Type} (φ : GateOp → List α → α) (d : α)
      (gs : List Gate) (xs : List α) : List α :=
    gs.foldl (fun w g => w ++ [φ g.op (g.inputs.map fun i => w.getD i d)]) xs

  have run_snoc {α : Type} (φ : GateOp → List α → α) (d : α)
      (gs : List Gate) (g : Gate) (xs : List α) :
      run φ d (gs ++ [g]) xs = run φ d gs xs ++
        [φ g.op (g.inputs.map fun i => (run φ d gs xs).getD i d)] := by
    simp [run, List.foldl_append]

  have run_length {α : Type} (φ : GateOp → List α → α) (d : α)
      (gs : List Gate) (xs : List α) :
      (run φ d gs xs).length = xs.length + gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton gs g ih => simp [run_snoc, ih, Nat.add_assoc]

  have append_rel {α : Type} {n : ℕ} (p : Equiv.Perm (Fin n))
      (d v : α) (a b : List α) (hn : n ≤ a.length) (hlen : a.length = b.length)
      (h : ∀ i, a.getD (lift p i) d = b.getD i d) :
      ∀ i, (a ++ [v]).getD (lift p i) d = (b ++ [v]).getD i d := by
    intro i
    by_cases hi : i < a.length
    · rw [List.getD_append _ _ _ _ ((lift_lt p hn).mpr hi),
        List.getD_append _ _ _ _ (by omega)]
      exact h i
    · have hni : n ≤ i := by omega
      rw [lift_ge p hni, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen]

  have run_rename {α : Type} {n : ℕ} (p : Equiv.Perm (Fin n))
      (φ : GateOp → List α → α) (d : α) (gs : List Gate) (a b : List α)
      (ha : a.length = n) (hb : b.length = n)
      (h : ∀ i, a.getD (lift p i) d = b.getD i d) :
      ∀ i, (run φ d (gs.map (gate p)) a).getD (lift p i) d =
        (run φ d gs b).getD i d := by
    induction gs using List.reverseRecOn with
    | nil => simpa [run] using h
    | append_singleton gs g ih =>
      simp only [List.map_append, List.map_cons, List.map_nil, run_snoc]
      have hv : φ (gate p g).op
          ((gate p g).inputs.map fun i => (run φ d (gs.map (gate p)) a).getD i d) =
          φ g.op (g.inputs.map fun i => (run φ d gs b).getD i d) := by
        simp only [gate, List.map_map, Function.comp_def, ih]
      rw [hv]
      exact append_rel p d _ _ _ (by simp [run_length, ha])
        (by simp [run_length, ha, hb]) ih

  have ofFn_rel {α : Type} {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n → α) (d : α) :
      ∀ i, (List.ofFn x).getD (lift p i) d = (List.ofFn (x ∘ p)).getD i d := by
    intro i
    by_cases hi : i < n
    · rw [lift_input p ⟨i,hi⟩]
      rw [List.getD_eq_getElem _ _ (by simpa using (p ⟨i,hi⟩).isLt),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    · rw [lift_ge p (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]

  have wires {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
      ((circuit p C).wires (List.ofFn x)).getD (lift p w) false =
        (C.wires (List.ofFn (x ∘ p))).getD w false := by
    exact run_rename p GateOp.eval false C.gates (List.ofFn x) (List.ofFn (x ∘ p))
      (by simp) (by simp) (ofFn_rel p x false) w

  have eval {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
      (circuit p C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ p)) :=
    wires p C x C.output

  have size {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) :
      (circuit p C).size = C.size := by simp [circuit,size_def]

  have gateAt_eq {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (j : ℕ) :
      gateAt (circuit p C) j = gate p (gateAt C j) := by
    exact List.getD_map C.gates ⟨GateOp.or, []⟩ (gate p)

  have ao2 {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (h : IsAO2 n C) :
      IsAO2 n (circuit p C) := by
    rcases h with ⟨hao,hback,hlen⟩
    refine ⟨?_,?_,?_⟩
    · intro g hg
      change g ∈ C.gates.map (gate p) at hg
      obtain ⟨g0,hg0,heq⟩ := List.mem_map.mp hg
      subst g
      exact hao g0 hg0
    · intro j hj i hi
      rw [gateAt_eq] at hi
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
      apply (lift_lt p (by omega)).mpr
      apply hback j (by simpa [circuit] using hj) k hk
    · intro g hg
      change g ∈ C.gates.map (gate p) at hg
      obtain ⟨g0,hg0,heq⟩ := List.mem_map.mp hg
      subst g
      simpa [gate] using hlen g0 hg0

  have nodup {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit)
      (h : ∀ j < C.gates.length, (gateAt C j).inputs.Nodup) :
      ∀ j < (circuit p C).gates.length, (gateAt (circuit p C) j).inputs.Nodup := by
    intro j hj
    rw [gateAt_eq]
    exact (h j (by simpa [circuit] using hj)).map (lift_injective p)

  have opnd_eq {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (h : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) :
      opnd (circuit p C) j b = lift p (opnd C j b) := by
    have hl : (gateAt C j).inputs.length = 2 := by
      apply h.2.2
      rw [gateAt_def]
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hb : b.val < (gateAt C j).inputs.length := by simpa [hl] using b.isLt
    simp only [opnd_def, gateAt_eq, gate]
    rw [List.getD_eq_getElem _ _ (by simpa using hb), List.getD_eq_getElem _ _ hb]
    simp

  have pair_comp {n : ℕ} (p : Equiv.Perm (Fin n)) (u v : Fin n) :
      pairInput (p u) (p v) ∘ p = pairInput u v := by
    funext i
    simp only [pairInput_def, Function.comp_apply, p.injective.eq_iff]

  have pair_wire {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (w : ℕ) (u v : Fin n) :
      ((circuit p C).wires (List.ofFn (pairInput (p u) (p v)))).getD (lift p w) false =
        (C.wires (List.ofFn (pairInput u v))).getD w false := by
    simpa only [pair_comp] using wires p C (pairInput (p u) (p v)) w

  have gate_pair {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (j : ℕ) (u v : Fin n) :
      gateVal n (circuit p C) j (pairInput (p u) (p v)) =
        gateVal n C j (pairInput u v) := by
    simpa only [gateVal_def, lift_ge p (Nat.le_add_right n j)] using
      pair_wire p C (n+j) u v

  have opnd_pair {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (h : IsAO2 n C)
      (j : ℕ) (hj : j < C.gates.length) (b : Fin 2) (u v : Fin n) :
      ((circuit p C).wires (List.ofFn (pairInput (p u) (p v)))).getD
        (opnd (circuit p C) j b) false =
        (C.wires (List.ofFn (pairInput u v))).getD (opnd C j b) false := by
    rw [opnd_eq p C h j hj b]
    exact pair_wire p C (opnd C j b) u v

  have and_valid (C : Circuit) (j : ℕ) (h : (gateAt C j).op = GateOp.and) :
      j < C.gates.length := by
    by_contra hn
    have hj : C.gates[j]? = none := List.getElem?_eq_none (by omega)
    simp [gateAt_def,List.getD_eq_getElem?_getD,hj] at h

  have head {n : ℕ} (p : Equiv.Perm (Fin n)) (C : Circuit) (g : Gate)
      (h : C.gates.head? = some g) :
      (circuit p C).gates.head? = some (gate p g) := by
    simp only [circuit,List.head?_map,h,Option.map_some]

  have first_pair {n : ℕ} (C : Circuit) (h : IsAO2 n C)
      (hd : ∀ j < C.gates.length, (gateAt C j).inputs.Nodup) (hne : C.gates ≠ []) :
      ∃ (g : Gate) (a b : Fin n), C.gates.head? = some g ∧
        g.inputs = [a.val,b.val] ∧ a ≠ b ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
    cases hgs : C.gates with
    | nil => exact False.elim (hne hgs)
    | cons g gs =>
      have hg : g ∈ C.gates := by simp [hgs]
      have hlen := h.2.2 g hg
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hlen
      have hzero : gateAt C 0 = g := by simp [gateAt_def,hgs]
      have hlt : 0 < C.gates.length := by simp [hgs]
      have ha : a < n := by
        have := h.2.1 0 hlt a (by simp [hzero,hab])
        simpa using this
      have hb : b < n := by
        have := h.2.1 0 hlt b (by simp [hzero,hab])
        simpa using this
      have hneab : a ≠ b := by simpa [hzero,hab] using hd 0 hlt
      refine ⟨g,⟨a,ha⟩,⟨b,hb⟩,by simp [hgs],hab,?_,h.1 g hg⟩
      intro heq
      exact hneab (congrArg Fin.val heq)

  let rho : Fin 16 → Fin 14 → Fin 14 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], ![7, 13, 12, 11, 10, 9, 8, 0, 6, 5, 4, 3, 2, 1], ![0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11], ![7, 13, 10, 11, 12, 8, 9, 0, 6, 4, 5, 1, 2, 3], ![0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11], ![7, 13, 9, 11, 8, 12, 10, 0, 2, 5, 4, 1, 6, 3], ![0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13], ![7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1], ![0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13], ![7, 11, 12, 13, 9, 10, 8, 0, 5, 6, 2, 3, 4, 1], ![0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11], ![7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3], ![0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11], ![7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3], ![0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13], ![7, 11, 8, 13, 10, 9, 12, 0, 4, 2, 6, 3, 5, 1]]

  let inv : Fin 16 → Fin 14 → Fin 14 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], ![7, 13, 12, 11, 10, 9, 8, 0, 6, 5, 4, 3, 2, 1], ![0, 1, 4, 3, 2, 6, 5, 7, 8, 10, 9, 13, 12, 11], ![7, 11, 12, 13, 9, 10, 8, 0, 5, 6, 2, 3, 4, 1], ![0, 1, 5, 3, 6, 2, 4, 7, 12, 9, 10, 13, 8, 11], ![7, 11, 8, 13, 10, 9, 12, 0, 4, 2, 6, 3, 5, 1], ![0, 1, 6, 3, 5, 4, 2, 7, 12, 10, 9, 11, 8, 13], ![7, 13, 8, 11, 9, 10, 12, 0, 2, 4, 5, 3, 6, 1], ![0, 3, 2, 1, 5, 4, 6, 7, 9, 8, 12, 11, 10, 13], ![7, 13, 10, 11, 12, 8, 9, 0, 6, 4, 5, 1, 2, 3], ![0, 3, 5, 1, 2, 6, 4, 7, 9, 12, 8, 13, 10, 11], ![7, 11, 10, 13, 8, 12, 9, 0, 4, 6, 2, 1, 5, 3], ![0, 3, 4, 1, 6, 2, 5, 7, 10, 8, 12, 13, 9, 11], ![7, 11, 9, 13, 12, 8, 10, 0, 5, 2, 6, 1, 4, 3], ![0, 3, 6, 1, 4, 5, 2, 7, 10, 12, 8, 11, 9, 13], ![7, 13, 9, 11, 8, 12, 10, 0, 2, 5, 4, 1, 6, 3]]

  let reps : List (List Nat) := [[0,1], [0,2], [0,7], [0,8], [0,11], [1,2], [1,3], [1,8], [1,9], [1,11], [2,4], [2,6], [2,8], [2,10]]

  let masks : List Nat := [127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256]

  let adjacent (a b : Fin 14) : Bool := decide
   ((a.val < 7 ∧ 7 ≤ b.val ∧ (a.val + 14 - b.val) % 7 ∈ ([0,1,3] : List Nat)) ∨
    (b.val < 7 ∧ 7 ≤ a.val ∧ (b.val + 14 - a.val) % 7 ∈ ([0,1,3] : List Nat)))

  let fano (x : Fin 14 → Bool) : Bool := decide
   (∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

  have inverse_cert : ∀ k : Fin 16, ∀ a : Fin 14,
   inv k (rho k a) = a ∧ rho k (inv k a) = a := by
    refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))))))))))))))))
    all_goals decide +kernel

  have endpoint_cert : ∀ k : Fin 16,
   (rho k 0 = 0 ∧ rho k 7 = 7) ∨ (rho k 0 = 7 ∧ rho k 7 = 0) := by decide +kernel

  have edge_cert : ∀ k : Fin 16, ∀ a b : Fin 14,
   adjacent (rho k a) (rho k b) = adjacent a b := by
    refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))))))))))))))))
    all_goals decide +kernel

  have orbit_cert : ∀ a b : Fin 14, a ≠ b → ∃ k : Fin 16,
   [(rho k a).val, (rho k b).val] ∈ reps ∨ [(rho k b).val, (rho k a).val] ∈ reps := by
    refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))))))))))))))
    all_goals decide +kernel

  have edge_bridge : ∀ a b : Fin 14, adjacent a b = true ↔
   ∃ p l : Fin 7, p ∈ fanoLines l ∧
   ((a = Fin.castAdd 7 p ∧ b = Fin.natAdd 7 l) ∨ (b = Fin.castAdd 7 p ∧ a = Fin.natAdd 7 l)) := by
    refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))))))))))))))
    all_goals decide +kernel

  have negative_cert : masks.all (fun m => !(fano fun i => m.testBit i.val)) = true := by decide +kernel

  have fano_edges (x : Fin 14 → Bool) : fano x =
      decide (∃ a b : Fin 14, adjacent a b = true ∧ x a = true ∧ x b = true) := by
    unfold fano
    congr 1
    apply propext
    constructor
    · rintro ⟨p,l,hedge,hp,hl⟩
      exact ⟨Fin.castAdd 7 p,Fin.natAdd 7 l,
        (edge_bridge _ _).mpr ⟨p,l,hedge,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
    · rintro ⟨a,b,hedge,ha,hb⟩
      obtain ⟨p,l,hpl,hd⟩ := (edge_bridge a b).mp hedge
      rcases hd with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨p,l,hpl,ha,hb⟩
      · exact ⟨p,l,hpl,hb,ha⟩

  have invariance (k : Fin 16) (x : Fin 14 → Bool) :
      fano (fun i => x (rho k i)) = fano x := by
    rw [fano_edges (fun i => x (rho k i)), fano_edges x]
    congr 1
    apply propext
    constructor
    · rintro ⟨a,b,hedge,ha,hb⟩
      exact ⟨rho k a,rho k b,(edge_cert k a b).trans hedge,ha,hb⟩
    · rintro ⟨a,b,hedge,ha,hb⟩
      refine ⟨inv k a,inv k b,?_,?_,?_⟩
      · have he := edge_cert k (inv k a) (inv k b)
        rw [(inverse_cert k a).2,(inverse_cert k b).2] at he
        exact he.symm.trans hedge
      · simpa only [(inverse_cert k a).2] using ha
      · simpa only [(inverse_cert k b).2] using hb

  let F (x : Fin 14 → Bool) : Bool := decide (∃ p l : Fin 7,
   p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

  have F_single (a : Fin 14) : F (pairInput a a) = false := by
    have h : ∀ a : Fin 14, F (pairInput a a) = false := by decide +kernel
    exact h a

  have F_pair (p l : Fin 7) (hp : p ∈ fanoLines l) :
   F (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l)) = true := by
   simp only [F,decide_eq_true_eq]
   exact ⟨p,l,hp,by simp [pairInput_def],by simp [pairInput_def]⟩

  have circuit_nonempty (C : Circuit) (hs : circuitFun 14 C = F) : C.gates ≠ [] := by
   intro hn
   have hsingle (a : Fin 14) : C.eval (List.ofFn (pairInput a a)) = false := by
     have h := congrFun hs (pairInput a a)
     exact h.trans (F_single a)
   have hpair : C.eval (List.ofFn (pairInput (0 : Fin 14) 7)) = true := by
     have h := congrFun hs (pairInput (0 : Fin 14) 7)
     exact h.trans (F_pair 0 0 (by decide))
   by_cases ho : C.output < 14
   · have h := hsingle ⟨C.output,ho⟩
     simp only [eval_def,wires_def,hn,List.foldl_nil] at h
     rw [List.getD_eq_getElem _ _ (by simpa using ho),List.getElem_ofFn] at h
     simp [pairInput_def] at h
   · have hlen : (List.ofFn (pairInput (0 : Fin 14) 7)).length ≤ C.output := by simp;omega
     simp only [eval_def,wires_def,hn,List.foldl_nil] at hpair
     rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none hlen] at hpair
     cases hpair

  let packed : List Nat := [2111159234527359,4675347059835475,9350660026287268,13230028855838916,19181020142586886,27075955222729233,37332865189321860,45082562460688914,64214953892392450,16256]

  have packed_cert : ∀ k : Fin 37, ∀ i : Fin 14,
   (packed.getD (k.val / 4) 0).testBit (14 * (k.val % 4) + i.val) =
   (masks.getD k.val 0).testBit i.val := by
    refine (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))))))))))))))))))))))))))))))))))))
    all_goals decide +kernel

  have pair_symm (u v : Fin 14) : pairInput u v = pairInput v u := by
   funext w
   simp only [pairInput_def, or_comm]

  have masks_pair :
   (fun i : Fin 14 => (129 : Nat).testBit i.val) = pairInput 0 7 ∧
   (fun i : Fin 14 => (1 : Nat).testBit i.val) = pairInput 0 0 ∧
   (fun i : Fin 14 => (128 : Nat).testBit i.val) = pairInput 7 7 := by decide +kernel

  dsimp only
  intro C hsize hAO hND hspec hshared hdeg0 hdeg7 j hAndJ hcone hPair hSingles
  change circuitFun 14 C = fano at hspec
  have hne : C.gates ≠ [] := circuit_nonempty C hspec
  obtain ⟨g,a,b,hhead,hin,hab,hop⟩ := first_pair C hAO hND hne
  obtain ⟨k,hcanon⟩ := orbit_cert a b hab
  let p : Equiv.Perm (Fin 14) := {
    toFun := rho k
    invFun := inv k
    left_inv := fun a => (inverse_cert k a).1
    right_inv := fun a => (inverse_cert k a).2 }
  let D := circuit p C
  have hdsize : D.size ≤ 27 := by
    rw [size]
    exact hsize
  have hdAO : IsAO2 14 D := ao2 p C hAO
  have hdND : ∀ g ∈ D.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_iff_getElem.mp hg
    have h := nodup p C hND t ht
    change (gateAt D t).inputs.Nodup at h
    simpa only [gateAt_def,List.getD_eq_getElem _ _ ht] using h
  have hdSpec : circuitFun 14 D = fano := by
    funext x
    change D.eval (List.ofFn x) = fano x
    rw [eval]
    change circuitFun 14 C (x ∘ p) = fano x
    rw [hspec]
    exact invariance k x
  have hPos : ∀ q l : Fin 7, q ∈ fanoLines l →
      D.eval (List.ofFn (pairInput (Fin.castAdd 7 q) (Fin.natAdd 7 l))) = true := by
    intro q l hq
    have he := congrFun hdSpec (pairInput (Fin.castAdd 7 q) (Fin.natAdd 7 l))
    exact he.trans (F_pair q l hq)
  have hNeg : ∀ q : Fin 37, D.eval (List.ofFn fun i : Fin 14 =>
      (packed.getD (q.val / 4) 0).testBit (14 * (q.val % 4) + i.val)) = false := by
    intro q
    simp only [packed_cert]
    have hq : masks.getD q.val 0 ∈ masks := by
      have hb : q.val < masks.length := q.isLt
      rw [List.getD_eq_getElem _ _ hb]
      exact List.getElem_mem hb
    have hn := (List.all_eq_true.mp negative_cert) _ hq
    have hf : fano (fun i => (masks.getD q.val 0).testBit i.val) = false := by
      simpa using hn
    exact (congrFun hdSpec _).trans hf
  have hdhead : D.gates.head? = some (gate p g) :=
    head p C g hhead
  have hdinputs : (gate p g).inputs =
      [(rho k a).val,(rho k b).val] := by
    simp only [gate,hin,List.map_cons,List.map_nil,
      lift_input]
    rfl
  have hdcanon : (gate p g).inputs ∈ reps ∨
      (gate p g).inputs.reverse ∈ reps := by
    rw [hdinputs]
    simpa using hcanon
  have hj : j < C.gates.length := and_valid C j hAndJ
  have hdAndJ : (gateAt D j).op = GateOp.and := by
    rw [gateAt_eq]
    exact hAndJ
  have hdPair : gateVal 14 D j (pairInput (0 : Fin 14) 7) = true := by
    have he := gate_pair p C j (0 : Fin 14) 7
    have hend := endpoint_cert k
    rcases hend with ⟨h0,h7⟩ | ⟨h0,h7⟩
    · simpa only [show p 0 = 0 from h0,show p 7 = 7 from h7] using he.trans hPair
    · simpa only [show p 0 = 7 from h0,show p 7 = 0 from h7,pair_symm 7 0] using he.trans hPair
  have hdSingles : ∀ b : Fin 2,
      wireVal 14 D (opnd D j b) (pairInput (0 : Fin 14) 0) = false ∧
      wireVal 14 D (opnd D j b) (pairInput (7 : Fin 14) 7) = false := by
    intro t
    have h0 := opnd_pair p C hAO j hj t (0 : Fin 14) 0
    have h7 := opnd_pair p C hAO j hj t (7 : Fin 14) 7
    change wireVal 14 D (opnd D j t) (pairInput (p 0) (p 0)) =
      wireVal 14 C (opnd C j t) (pairInput 0 0) at h0
    change wireVal 14 D (opnd D j t) (pairInput (p 7) (p 7)) =
      wireVal 14 C (opnd C j t) (pairInput 7 7) at h7
    rcases endpoint_cert k with ⟨hp0,hp7⟩ | ⟨hp0,hp7⟩
    · exact ⟨by simpa only [show p 0 = 0 from hp0] using h0.trans (hSingles t).1,
        by simpa only [show p 7 = 7 from hp7] using h7.trans (hSingles t).2⟩
    · exact ⟨by simpa only [show p 7 = 0 from hp7] using h7.trans (hSingles t).2,
        by simpa only [show p 0 = 7 from hp0] using h0.trans (hSingles t).1⟩
  have hbitPair : (D.wires (List.ofFn fun i : Fin 14 => (129 : Nat).testBit i.val)).getD (14+j) false = true := by
    rw [masks_pair.1]
    exact hdPair
  have hbitSingle : ∀ b : Fin 2,
      (D.wires (List.ofFn fun i : Fin 14 => (1 : Nat).testBit i.val)).getD (opnd D j b) false = false ∧
      (D.wires (List.ofFn fun i : Fin 14 => (128 : Nat).testBit i.val)).getD (opnd D j b) false = false := by
    rw [masks_pair.2.1,masks_pair.2.2]
    exact hdSingles
  rcases hop with hop | hop
  · exact hAnd D hdsize hdAO hdND
      ⟨_,hdhead,hop,hdcanon⟩ hPos hNeg j hdAndJ hbitPair hbitSingle
  · exact hOr D hdsize hdAO hdND
      ⟨_,hdhead,hop,hdcanon⟩ hPos hNeg j hdAndJ hbitPair hbitSingle
