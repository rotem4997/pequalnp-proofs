import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2130_1
    (h1 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true}
        ≤ 10 * C.size)
    (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true}
        ≤ 10 * C.size)
    (h3 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) C
          (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false}
        ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true } := by
  classical
  intro q N I instI C hq hN hcol huniq hmin hsound D edge T hT
  let n : ℕ := N + N
  let A : Finset (Fin C.size) := Finset.univ.filter fun j =>
    (C.wires (List.replicate n false)).getD (n + j.val) false = false ∧
    ∃ l : Fin N, ∃ p ∈ T l, (C.wires (List.ofFn (edge p l))).getD (n + j.val) false = true
  have hAcard : Fintype.card {x16 : Fin C.size //
      (C.wires (List.replicate n false)).getD (n + ↑x16) false = false ∧
      ∃ x17 : Fin N, ∃ x18 ∈ T x17, (C.wires (List.ofFn (edge x18 x17))).getD (n + ↑x16) false = true} = A.card := by
    rw [Fintype.card_subtype]
  rw [hAcard]
  by_cases hTempty : ∀ l : Fin N, T l = ∅
  · simp [hTempty]
  push Not at hTempty
  obtain ⟨l₀, hl₀ne⟩ := hTempty
  obtain ⟨p₀, hp₀⟩ := hl₀ne
  have hmono : Monotone2 C := hmin.1
  let runW : List Gate → List Bool → List Bool := fun gs x =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hrun_nil : ∀ x, runW [] x = x := fun _ => rfl
  have hrun_snoc : ∀ gs g x, runW (gs ++ [g]) x =
      runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)] := by
    intro gs g x
    simp [runW]
  have hrun_append : ∀ g1 g2 x, runW (g1 ++ g2) x = runW g2 (runW g1 x) := by
    intro g1 g2 x
    simp [runW]
  have hrun_len : ∀ gs x, (runW gs x).length = x.length + gs.length := by
    intro gs x
    induction gs using List.reverseRecOn with
    | nil => simp [runW]
    | append_singleton gs g ih =>
      rw [hrun_snoc, List.length_append, List.length_singleton, ih, List.length_append, List.length_singleton]
      omega
  have hrun_prefix_getD : ∀ g1 g2 x i, i < x.length + g1.length →
      (runW (g1 ++ g2) x).getD i false = (runW g1 x).getD i false := by
    intro g1 g2 x i hi
    induction g2 using List.reverseRecOn with
    | nil => simp
    | append_singleton g2 g ih =>
      rw [← List.append_assoc, hrun_snoc, List.getD_eq_getElem?_getD, List.getElem?_append_left]
      · rw [← List.getD_eq_getElem?_getD]
        exact ih
      · rw [hrun_len, List.length_append]
        omega
  have hrun_gate_getD : ∀ gs x k (hk : k < gs.length),
      (runW gs x).getD (x.length + k) false =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (runW (gs.take k) x).getD i false) := by
    intro gs x k hk
    have hsplit : gs = gs.take k ++ [gs[k]'hk] ++ gs.drop (k + 1) := by
      rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]
    conv_lhs => rw [hsplit]
    have hlenk : (gs.take k).length = k := List.length_take_of_le hk.le
    rw [hrun_prefix_getD (gs.take k ++ [gs[k]'hk]) (gs.drop (k + 1)) x (x.length + k)
      (by simp; omega)]
    rw [hrun_snoc]
    have hlenw : (runW (gs.take k) x).length = x.length + k := by rw [hrun_len, hlenk]
    rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
    rfl
  have heval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have heval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have hrun_mono : ∀ gs, (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ x y : List Bool, x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (runW gs x).getD i false = true → (runW gs y).getD i false = true := by
    intro gs hgs x y hxy hle
    induction gs using List.reverseRecOn with
    | nil => exact hle
    | append_singleton gs g ih =>
      have hgs' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
        fun g' hg' => hgs g' (List.mem_append_left _ hg')
      have ih' := ih hgs'
      have hlen_eq : (runW gs x).length = (runW gs y).length := by rw [hrun_len, hrun_len, hxy]
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
      intro i hi
      rw [hrun_snoc] at hi ⊢
      by_cases hlt : i < (runW gs x).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD] at hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
        exact ih' i hi
      · by_cases heq : i = (runW gs x).length
        · subst heq
          rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
          rw [hlen_eq, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
          simp only [Option.getD_some] at hi ⊢
          rcases hg with hop | hop <;> rw [hop] at hi ⊢
          · simp only [heval_and, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            rintro b ⟨j, hj, rfl⟩
            exact ih' j (hi _ ⟨j, hj, rfl⟩)
          · simp only [heval_or, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            obtain ⟨_, ⟨j, hj, rfl⟩, htrue⟩ := hi
            exact ⟨_, ⟨j, hj, rfl⟩, ih' j htrue⟩
        · have hge : (runW gs x ++ [g.op.eval (g.inputs.map fun i => (runW gs x).getD i false)]).length ≤ i := by
            simp; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hi
          cases hi
  have hC_ao : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases (hmono g hg).1 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hw0_le : ∀ z : Fin n → Bool, ∀ w,
      (C.wires (List.replicate n false)).getD w false = true →
      (C.wires (List.ofFn z)).getD w false = true := by
    intro z w hw
    exact hrun_mono C.gates hC_ao (List.replicate n false) (List.ofFn z) (by simp)
      (fun i hi => by
        by_cases hlt : i < n
        · simp [List.getD_eq_getElem?_getD, hlt] at hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          cases hi) w hw
  have hw0_out : (C.wires (List.replicate n false)).getD C.output false = false := by
    have h0 : circuitFun n C (fun _ => false) = false := by
      apply hsound (fun _ => false)
      · simp
      · rintro ⟨_, _, _, h, _⟩
        cases h
    have hrep : List.ofFn (fun _ : Fin n => false) = List.replicate n false := List.ofFn_const _ _
    change (C.wires (List.ofFn (fun _ : Fin n => false))).getD C.output false = false at h0
    rwa [hrep] at h0
  let w0 : ℕ → Bool := fun w => (C.wires (List.replicate n false)).getD w false
  let wpl : Fin N → Fin N → ℕ → Bool := fun p l w => (C.wires (List.ofFn (edge p l))).getD w false
  let evalTag : List Bool → Bool ⊕ ℕ → Bool := fun ws t =>
    Sum.elim id (fun i => ws.getD i false) t
  let toOpt : Bool ⊕ ℕ → Option ℕ := Sum.elim (fun _ => none) some
  let step : (List Gate × (ℕ → Bool ⊕ ℕ)) → ℕ → (List Gate × (ℕ → Bool ⊕ ℕ)) := fun st k =>
    let gs := st.1
    let mp := st.2
    if w0 (n + k) = true then
      (gs, Function.update mp (n + k) (Sum.inl true))
    else if ¬ ∃ l : Fin N, ∃ p ∈ T l, wpl p l (n + k) = true then
      (gs, Function.update mp (n + k) (Sum.inl false))
    else
      let g := C.gates.getD k ⟨GateOp.or, []⟩
      let tagOf : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then mp i else Sum.inl false
      let ws : List ℕ := g.inputs.filterMap (fun i => toOpt (tagOf i))
      if ws.length = 1 then
        (gs, Function.update mp (n + k) (Sum.inr (ws.getD 0 0)))
      else if ws.length = 2 then
        (gs ++ [Gate.mk g.op [ws.getD 0 0, ws.getD 1 0]], Function.update mp (n + k) (Sum.inr (n + gs.length)))
      else
        (gs, Function.update mp (n + k) (Sum.inl false))
  let build : ℕ → (List Gate × (ℕ → Bool ⊕ ℕ)) := fun k =>
    (List.range k).foldl step ([], Sum.inr)
  have hbuild_succ : ∀ k, build (k + 1) = step (build k) k := by
    intro k
    simp [build, List.range_succ]
  have hInv : ∀ k ≤ C.gates.length,
      let st := build k
      let gs := st.1
      let mp := st.2
      gs.length ≤ (A.filter fun j => j.val < k).card ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
      (∀ w < n + k, Sum.elim (fun _ => True) (fun i => i < n + gs.length) (mp w)) ∧
      (∀ w < n + k, mp w = Sum.inl true → w0 w = true) ∧
      (∀ (z : Fin n → Bool) (w : ℕ), w < n + k →
        evalTag (runW gs (List.ofFn z)) (mp w) = true → (C.wires (List.ofFn z)).getD w false = true) ∧
      (∀ (l : Fin N) (p : Fin N), p ∈ T l → ∀ w < n + k,
        evalTag (runW gs (List.ofFn (edge p l))) (mp w) = wpl p l w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp [build], by simp [build], by simp [build], ?_, ?_, ?_, ?_⟩
      · intro w hw
        simpa [build] using hw
      · intro w _ h
        simp [build] at h
      · intro z w hw hev
        simp only [build, List.range_zero, List.foldl_nil, evalTag, hrun_nil] at hev
        have hpr := hrun_prefix_getD [] C.gates (List.ofFn z) w (by simp; omega)
        change (runW C.gates (List.ofFn z)).getD w false = true
        rw [show C.gates = [] ++ C.gates from rfl, hpr, hrun_nil]
        exact hev
      · intro l p _ w hw
        simp only [build, List.range_zero, List.foldl_nil, evalTag, hrun_nil]
        have hpr := hrun_prefix_getD [] C.gates (List.ofFn (edge p l)) w (by simp; omega)
        change (List.ofFn (edge p l)).getD w false = (runW C.gates (List.ofFn (edge p l))).getD w false
        rw [show C.gates = [] ++ C.gates from rfl, hpr, hrun_nil]
    | succ k ih =>
      intro hk
      obtain ⟨hsz, hao, hrb, hbd, htr, hup, hex⟩ := ih (Nat.le_of_succ_le hk)
      set gs := (build k).1
      set mp := (build k).2
      have hklt : k < C.gates.length := Nat.lt_of_succ_le hk
      have hsub_A : (A.filter fun j => j.val < k) ⊆ (A.filter fun j => j.val < k + 1) := by
        intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, Nat.lt_succ_of_lt hj.2⟩
      have hsz_le : gs.length ≤ (A.filter fun j => j.val < k + 1).card :=
        hsz.trans (Finset.card_le_card hsub_A)
      rw [hbuild_succ]
      change let st := step (gs, mp) k; _
      by_cases hw0k : w0 (n + k) = true
      · have hst : step (gs, mp) k = (gs, Function.update mp (n + k) (Sum.inl true)) := by
          simp [step, hw0k]
        rw [hst]
        dsimp only
        refine ⟨hsz_le, hao, hrb, ?_, ?_, ?_, ?_⟩
        · intro w hw
          by_cases hwk : w = n + k
          · subst hwk; simp
          · rw [Function.update_of_ne hwk]; exact hbd w (by omega)
        · intro w hw h1
          by_cases hwk : w = n + k
          · subst hwk; exact hw0k
          · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
        · intro z w hw hev
          by_cases hwk : w = n + k
          · subst hwk; exact hw0_le z (n + k) hw0k
          · rw [Function.update_of_ne hwk] at hev; exact hup z w (by omega) hev
        · intro l p hp w hw
          by_cases hwk : w = n + k
          · subst hwk
            simp only [Function.update_self, evalTag]
            exact (hw0_le (edge p l) (n + k) hw0k).symm
          · rw [Function.update_of_ne hwk]; exact hex l p hp w (by omega)
      · have hw0kf : w0 (n + k) = false := Bool.eq_false_iff.mpr hw0k
        by_cases hact : ∃ l : Fin N, ∃ p ∈ T l, wpl p l (n + k) = true
        · set g := C.gates.getD k ⟨GateOp.or, []⟩
          have hg_eq : g = C.gates[k]'hklt := List.getD_eq_getElem C.gates _ hklt
          have hg_mem : g ∈ C.gates := hg_eq ▸ List.getElem_mem hklt
          have hg_ao : g.op = GateOp.and ∨ g.op = GateOp.or := hC_ao g hg_mem
          have hg_len : g.inputs.length ≤ 2 := (hmono g hg_mem).2
          let tagOf : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then mp i else Sum.inl false
          have htag_bd : ∀ i w, tagOf i = Sum.inr w → w < n + gs.length := by
            intro i w htw
            by_cases hi : i < n + k
            · have hb := hbd i hi
              simp only [tagOf, hi, ↓reduceIte] at htw
              rw [htw] at hb
              exact hb
            · simp [tagOf, hi] at htw
          have htag_tr : ∀ i, tagOf i = Sum.inl true → i < n + k ∧ w0 i = true := by
            intro i hti
            by_cases hi : i < n + k
            · simp only [tagOf, hi, ↓reduceIte] at hti
              exact ⟨hi, htr i hi hti⟩
            · simp [tagOf, hi] at hti
          have htag_up : ∀ (z : Fin n → Bool) (i : ℕ),
              evalTag (runW gs (List.ofFn z)) (tagOf i) = true →
              (runW (C.gates.take k) (List.ofFn z)).getD i false = true := by
            intro z i hev
            by_cases hi : i < n + k
            · simp only [tagOf, hi, ↓reduceIte] at hev
              have hc := hup z i hi hev
              have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
              have hpr := hrun_prefix_getD (C.gates.take k) (C.gates.drop k) (List.ofFn z) i
                (by simp [hlenk]; omega)
              rw [List.take_append_drop] at hpr
              rw [← hpr]
              exact hc
            · simp [tagOf, hi, evalTag] at hev
          have htag_ex : ∀ (l : Fin N) (p : Fin N), p ∈ T l → ∀ i : ℕ,
              evalTag (runW gs (List.ofFn (edge p l))) (tagOf i) =
              (runW (C.gates.take k) (List.ofFn (edge p l))).getD i false := by
            intro l p hp i
            by_cases hi : i < n + k
            · simp only [tagOf, hi, ↓reduceIte]
              rw [hex l p hp i hi]
              have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
              have hpr := hrun_prefix_getD (C.gates.take k) (C.gates.drop k) (List.ofFn (edge p l)) i
                (by simp [hlenk]; omega)
              rw [List.take_append_drop] at hpr
              exact hpr
            · simp only [tagOf, hi, ↓reduceIte, evalTag]
              have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
              have hge : (runW (C.gates.take k) (List.ofFn (edge p l))).length ≤ i := by
                rw [hrun_len, List.length_ofFn, hlenk]; omega
              symm
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
              rfl
          have hC_eval_z : ∀ (z : Fin n → Bool),
              (C.wires (List.ofFn z)).getD (n + k) false =
              g.op.eval (g.inputs.map fun i => (runW (C.gates.take k) (List.ofFn z)).getD i false) := by
            intro z
            have h := hrun_gate_getD C.gates (List.ofFn z) k hklt
            rw [List.length_ofFn] at h
            rw [← hg_eq] at h
            exact h
          have hC_eval_0 : w0 (n + k) =
              g.op.eval (g.inputs.map fun i => (runW (C.gates.take k) (List.replicate n false)).getD i false) := by
            have h := hrun_gate_getD C.gates (List.replicate n false) k hklt
            rw [List.length_replicate] at h
            rw [← hg_eq] at h
            exact h
          have hC_take_0 : ∀ i < n + k,
              (runW (C.gates.take k) (List.replicate n false)).getD i false = w0 i := by
            intro i hi
            have hlenk : (C.gates.take k).length = k := List.length_take_of_le hklt.le
            have hpr := hrun_prefix_getD (C.gates.take k) (C.gates.drop k) (List.replicate n false) i
              (by simp [hlenk]; omega)
            rw [List.take_append_drop] at hpr
            exact hpr.symm
          obtain ⟨l₁, p₁, hp₁, hw₁⟩ := hact
          have hC_eval_1 : g.op.eval (g.inputs.map fun i => evalTag (runW gs (List.ofFn (edge p₁ l₁))) (tagOf i)) = true := by
            have heq : (g.inputs.map fun i => evalTag (runW gs (List.ofFn (edge p₁ l₁))) (tagOf i)) =
                (g.inputs.map fun i => (runW (C.gates.take k) (List.ofFn (edge p₁ l₁))).getD i false) :=
              List.map_congr_left (fun i _ => htag_ex l₁ p₁ hp₁ i)
            rw [heq, ← hC_eval_z (edge p₁ l₁)]
            exact hw₁
          have hjk_mem : (⟨k, hklt⟩ : Fin C.size) ∈ A.filter (fun j => j.val < k + 1) := by
            simp only [Finset.mem_filter, A, Finset.mem_univ, true_and]
            exact ⟨⟨hw0kf, l₁, p₁, hp₁, hw₁⟩, Nat.lt_succ_self k⟩
          have hjk_not : (⟨k, hklt⟩ : Fin C.size) ∉ A.filter (fun j => j.val < k) := by
            simp
          have hcard_inc : (A.filter fun j => j.val < k).card + 1 ≤
              (A.filter fun j => j.val < k + 1).card := by
            have hsub2 : insert (⟨k, hklt⟩ : Fin C.size) (A.filter fun j => j.val < k) ⊆
                A.filter (fun j => j.val < k + 1) := Finset.insert_subset hjk_mem hsub_A
            have hci := Finset.card_le_card hsub2
            rw [Finset.card_insert_of_notMem hjk_not] at hci
            exact hci
          set ws : List ℕ := g.inputs.filterMap (fun i => toOpt (tagOf i))
          have hws_not_nil : ws ≠ [] := by
            intro hnil
            have hall_inl : ∀ i ∈ g.inputs, ∃ b : Bool, tagOf i = Sum.inl b := by
              intro i hi
              cases ht : tagOf i with
              | inl b => exact ⟨b, rfl⟩
              | inr w =>
                have hmem : w ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                rw [hnil] at hmem
                simp at hmem
            rcases hg_ao with hop | hop
            · rw [hop] at hC_eval_1 hC_eval_0
              have hall_t : ∀ i ∈ g.inputs, tagOf i = Sum.inl true := by
                intro i hi
                obtain ⟨b, hb⟩ := hall_inl i hi
                cases b
                · simp only [heval_and, List.all_eq_true, List.mem_map, id_eq] at hC_eval_1
                  have hff := hC_eval_1 _ ⟨i, hi, rfl⟩
                  simp [hb, evalTag] at hff
                · exact hb
              have h0t : w0 (n + k) = true := by
                rw [hC_eval_0]
                simp only [heval_and, List.all_eq_true, List.mem_map, id_eq]
                rintro _ ⟨i, hi, rfl⟩
                obtain ⟨hlti, hw0i⟩ := htag_tr i (hall_t i hi)
                rw [hC_take_0 i hlti]
                exact hw0i
              rw [hw0kf] at h0t
              cases h0t
            · rw [hop] at hC_eval_1 hC_eval_0
              simp only [heval_or, List.any_eq_true, List.mem_map, id_eq] at hC_eval_1
              obtain ⟨_, ⟨i, hi, rfl⟩, htrue⟩ := hC_eval_1
              obtain ⟨b, hb⟩ := hall_inl i hi
              cases b
              · simp [hb, evalTag] at htrue
              · obtain ⟨hlti, hw0i⟩ := htag_tr i hb
                have h0t : w0 (n + k) = true := by
                  rw [hC_eval_0]
                  simp only [heval_or, List.any_eq_true, List.mem_map, id_eq]
                  exact ⟨_, ⟨i, hi, rfl⟩, by rw [hC_take_0 i hlti]; exact hw0i⟩
                rw [hw0kf] at h0t
                cases h0t
          have hws_len : ws.length ≤ 2 := (List.length_filterMap_le _ _).trans hg_len
          have hws_cases : (∃ a, ws = [a]) ∨ (∃ a b, ws = [a, b]) := by
            rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · exact absurd rfl hws_not_nil
            · exact Or.inl ⟨a, rfl⟩
            · exact Or.inr ⟨a, b, rfl⟩
            · simp at hws_len
          rcases hws_cases with ⟨a, hwa⟩ | ⟨a, b, hwab⟩
          · have hst_a : step (gs, mp) k = (gs, Function.update mp (n + k) (Sum.inr a)) := by
              have hact' : ∃ l : Fin N, ∃ p ∈ T l, wpl p l (n + k) = true := ⟨l₁, p₁, hp₁, hw₁⟩
              simp only [step, hw0kf, Bool.false_eq_true, ↓reduceIte, hact', not_true_eq_false]
              change (if ws.length = 1 then (gs, Function.update mp (n + k) (Sum.inr (ws.getD 0 0)))
                else if ws.length = 2 then (gs ++ [Gate.mk g.op [ws.getD 0 0, ws.getD 1 0]],
                  Function.update mp (n + k) (Sum.inr (n + gs.length)))
                else (gs, Function.update mp (n + k) (Sum.inl false))) = _
              rw [hwa]
              rfl
            rw [hst_a]
            dsimp only
            have ha_mem : a ∈ ws := by rw [hwa]; simp
            obtain ⟨ia, hia_mem, hia_tag⟩ := List.mem_filterMap.mp ha_mem
            have hia_inr : tagOf ia = Sum.inr a := by
              cases ht : tagOf ia with
              | inl _ => simp [ht, toOpt] at hia_tag
              | inr w =>
                simp only [ht, toOpt, Sum.elim_inr, Option.some.injEq] at hia_tag
                exact congrArg Sum.inr hia_tag
            have ha_lt : a < n + gs.length := htag_bd ia a hia_inr
            refine ⟨hsz_le, hao, hrb, ?_, ?_, ?_, ?_⟩
            · intro w hw
              by_cases hwk : w = n + k
              · subst hwk; simpa using ha_lt
              · rw [Function.update_of_ne hwk]; exact hbd w (by omega)
            · intro w hw h1
              by_cases hwk : w = n + k
              · subst hwk; simp at h1
              · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
            · intro z w hw hev
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr] at hev
                rw [hC_eval_z z]
                rcases hg_ao with hop | hop <;> rw [hop]
                · simp only [heval_and, List.all_eq_true, List.mem_map, id_eq]
                  rintro _ ⟨i, hi, rfl⟩
                  cases ht : tagOf i with
                  | inl b =>
                    cases b
                    · rw [hop] at hC_eval_1
                      simp only [heval_and, List.all_eq_true, List.mem_map, id_eq] at hC_eval_1
                      have hf := hC_eval_1 _ ⟨i, hi, rfl⟩
                      simp [ht, evalTag] at hf
                    · exact htag_up z i (by simp [ht, evalTag])
                  | inr w' =>
                    have hw'mem : w' ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                    rw [hwa, List.mem_singleton] at hw'mem
                    subst hw'mem
                    exact htag_up z i (by simp only [ht, evalTag, Sum.elim_inr]; exact hev)
                · simp only [heval_or, List.any_eq_true, List.mem_map, id_eq]
                  exact ⟨_, ⟨ia, hia_mem, rfl⟩, htag_up z ia (by simp only [hia_inr, evalTag, Sum.elim_inr]; exact hev)⟩
              · rw [Function.update_of_ne hwk] at hev; exact hup z w (by omega) hev
            · intro l p hp w hw
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr]
                rw [show wpl p l (n + k) = (C.wires (List.ofFn (edge p l))).getD (n + k) false from rfl]
                rw [hC_eval_z (edge p l)]
                have hmap : (g.inputs.map fun i => (runW (C.gates.take k) (List.ofFn (edge p l))).getD i false) =
                    (g.inputs.map fun i => evalTag (runW gs (List.ofFn (edge p l))) (tagOf i)) :=
                  List.map_congr_left (fun i _ => (htag_ex l p hp i).symm)
                rw [hmap]
                rcases hg_ao with hop | hop <;> rw [hop]
                · apply Bool.eq_iff_iff.mpr
                  simp only [heval_and, List.all_eq_true, List.mem_map, id_eq]
                  constructor
                  · rintro ha_t _ ⟨i, hi, rfl⟩
                    cases ht : tagOf i with
                    | inl b =>
                      cases b
                      · rw [hop] at hC_eval_1
                        simp only [heval_and, List.all_eq_true, List.mem_map, id_eq] at hC_eval_1
                        have hf := hC_eval_1 _ ⟨i, hi, rfl⟩
                        simp [ht, evalTag] at hf
                      · rfl
                    | inr w' =>
                      have hw'mem : w' ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                      rw [hwa, List.mem_singleton] at hw'mem
                      subst hw'mem
                      exact ha_t
                  · intro hall
                    have h1 := hall _ ⟨ia, hia_mem, rfl⟩
                    simpa [hia_inr, evalTag] using h1
                · apply Bool.eq_iff_iff.mpr
                  simp only [heval_or, List.any_eq_true, List.mem_map, id_eq]
                  constructor
                  · intro ha_t
                    exact ⟨_, ⟨ia, hia_mem, rfl⟩, by simpa [hia_inr, evalTag] using ha_t⟩
                  · rintro ⟨_, ⟨i, hi, rfl⟩, htrue⟩
                    cases ht : tagOf i with
                    | inl b =>
                      cases b
                      · simp [ht, evalTag] at htrue
                      · obtain ⟨hlti, hw0i⟩ := htag_tr i ht
                        have h0t : w0 (n + k) = true := by
                          rw [hC_eval_0, hop]
                          simp only [heval_or, List.any_eq_true, List.mem_map, id_eq]
                          exact ⟨_, ⟨i, hi, rfl⟩, by rw [hC_take_0 i hlti]; exact hw0i⟩
                        rw [hw0kf] at h0t
                        cases h0t
                    | inr w' =>
                      have hw'mem : w' ∈ ws := List.mem_filterMap.mpr ⟨i, hi, by simp [ht, toOpt]⟩
                      rw [hwa, List.mem_singleton] at hw'mem
                      subst hw'mem
                      simpa [ht, evalTag] using htrue
              · rw [Function.update_of_ne hwk]; exact hex l p hp w (by omega)
          · have hst_ab : step (gs, mp) k =
                (gs ++ [Gate.mk g.op [a, b]], Function.update mp (n + k) (Sum.inr (n + gs.length))) := by
              have hact' : ∃ l : Fin N, ∃ p ∈ T l, wpl p l (n + k) = true := ⟨l₁, p₁, hp₁, hw₁⟩
              simp only [step, hw0kf, Bool.false_eq_true, ↓reduceIte, hact', not_true_eq_false]
              change (if ws.length = 1 then (gs, Function.update mp (n + k) (Sum.inr (ws.getD 0 0)))
                else if ws.length = 2 then (gs ++ [Gate.mk g.op [ws.getD 0 0, ws.getD 1 0]],
                  Function.update mp (n + k) (Sum.inr (n + gs.length)))
                else (gs, Function.update mp (n + k) (Sum.inl false))) = _
              rw [hwab]
              rfl
            rw [hst_ab]
            dsimp only
            have hlen_inp : g.inputs.length = 2 := by
              have h1 := List.length_filterMap_le (fun i => toOpt (tagOf i)) g.inputs
              change ws.length ≤ g.inputs.length at h1
              rw [hwab] at h1
              simp at h1
              omega
            obtain ⟨i₀, i₁, hinp⟩ := List.length_eq_two.mp hlen_inp
            have hi₀₁ : tagOf i₀ = Sum.inr a ∧ tagOf i₁ = Sum.inr b := by
              have hfm : ws = [a, b] := hwab
              dsimp only [ws] at hfm
              rw [hinp] at hfm
              cases h0 : tagOf i₀ <;> cases h1 : tagOf i₁ <;> simp [h0, h1, toOpt] at hfm
              obtain ⟨rfl, rfl⟩ := hfm
              exact ⟨rfl, rfl⟩
            have ha_lt : a < n + gs.length := htag_bd i₀ a hi₀₁.1
            have hb_lt : b < n + gs.length := htag_bd i₁ b hi₀₁.2
            have hrun_keep : ∀ (x : List Bool) (w : ℕ), x.length = n → w < n + gs.length →
                (runW (gs ++ [⟨g.op, [a, b]⟩]) x).getD w false = (runW gs x).getD w false := by
              intro x w hx hw
              rw [hrun_prefix_getD gs [⟨g.op, [a, b]⟩] x w (by omega)]
            have hrun_new : ∀ (x : List Bool), x.length = n →
                (runW (gs ++ [⟨g.op, [a, b]⟩]) x).getD (n + gs.length) false =
                g.op.eval [(runW gs x).getD a false, (runW gs x).getD b false] := by
              intro x hx
              rw [hrun_snoc]
              have hlenw : (runW gs x).length = n + gs.length := by rw [hrun_len, hx]
              rw [← hlenw, List.getD_eq_getElem?_getD, List.getElem?_concat_length]
              rfl
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp only [List.length_append, List.length_singleton]
              omega
            · intro g' hg'
              simp only [List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact hao g' hg'
              · exact ⟨hg_ao, rfl⟩
            · intro j hj i hi
              simp only [List.length_append, List.length_singleton] at hj
              by_cases hjlt : j < gs.length
              · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt, ← List.getD_eq_getElem?_getD] at hi
                exact hrb j hjlt i hi
              · have hjeq : j = gs.length := by omega
                subst hjeq
                rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length] at hi
                simp only [Option.getD_some, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact ha_lt
                · exact hb_lt
            · intro w hw
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, Sum.elim_inr, List.length_append, List.length_singleton]
                omega
              · rw [Function.update_of_ne hwk]
                have hb := hbd w (by omega)
                cases hm : mp w with
                | inl _ => simp
                | inr u =>
                  rw [hm] at hb
                  simp only [Sum.elim_inr] at hb ⊢
                  simp only [List.length_append, List.length_singleton]
                  omega
            · intro w hw h1
              by_cases hwk : w = n + k
              · subst hwk; simp at h1
              · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
            · intro z w hw hev
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr] at hev
                rw [hrun_new (List.ofFn z) (by simp)] at hev
                rw [hC_eval_z z, hinp]
                simp only [List.map_cons, List.map_nil]
                rcases hg_ao with hop | hop <;> rw [hop] at hev ⊢
                · simp only [heval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hev ⊢
                  exact ⟨htag_up z i₀ (by simp only [hi₀₁.1, evalTag, Sum.elim_inr]; exact hev.1),
                    htag_up z i₁ (by simp only [hi₀₁.2, evalTag, Sum.elim_inr]; exact hev.2)⟩
                · simp only [heval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hev ⊢
                  rcases hev with h0 | h1
                  · exact Or.inl (htag_up z i₀ (by simp only [hi₀₁.1, evalTag, Sum.elim_inr]; exact h0))
                  · exact Or.inr (htag_up z i₁ (by simp only [hi₀₁.2, evalTag, Sum.elim_inr]; exact h1))
              · rw [Function.update_of_ne hwk] at hev
                apply hup z w (by omega)
                cases hm : mp w with
                | inl b => simpa [hm, evalTag] using hev
                | inr u =>
                  have hu := hbd w (by omega)
                  rw [hm] at hu hev
                  simp only [Sum.elim_inr] at hu
                  simp only [evalTag, Sum.elim_inr] at hev ⊢
                  rwa [hrun_keep (List.ofFn z) u (by simp) hu] at hev
            · intro l p hp w hw
              by_cases hwk : w = n + k
              · subst hwk
                simp only [Function.update_self, evalTag, Sum.elim_inr]
                rw [hrun_new (List.ofFn (edge p l)) (by simp [n])]
                rw [show wpl p l (n + k) = (C.wires (List.ofFn (edge p l))).getD (n + k) false from rfl]
                rw [hC_eval_z (edge p l), hinp]
                simp only [List.map_cons, List.map_nil]
                have e0 := htag_ex l p hp i₀
                have e1 := htag_ex l p hp i₁
                simp only [hi₀₁.1, hi₀₁.2, evalTag, Sum.elim_inr] at e0 e1
                rw [e0, e1]
              · rw [Function.update_of_ne hwk]
                rw [← hex l p hp w (by omega)]
                cases hm : mp w with
                | inl b => rfl
                | inr u =>
                  have hu := hbd w (by omega)
                  rw [hm] at hu
                  simp only [Sum.elim_inr] at hu
                  simp only [evalTag, Sum.elim_inr]
                  exact hrun_keep (List.ofFn (edge p l)) u (by simp [n]) hu
        · have hst : step (gs, mp) k = (gs, Function.update mp (n + k) (Sum.inl false)) := by
            simp [step, hw0kf, hact]
          rw [hst]
          dsimp only
          refine ⟨hsz_le, hao, hrb, ?_, ?_, ?_, ?_⟩
          · intro w hw
            by_cases hwk : w = n + k
            · subst hwk; simp
            · rw [Function.update_of_ne hwk]; exact hbd w (by omega)
          · intro w hw h1
            by_cases hwk : w = n + k
            · subst hwk; simp at h1
            · rw [Function.update_of_ne hwk] at h1; exact htr w (by omega) h1
          · intro z w hw hev
            by_cases hwk : w = n + k
            · subst hwk; simp [evalTag] at hev
            · rw [Function.update_of_ne hwk] at hev; exact hup z w (by omega) hev
          · intro l p hp w hw
            by_cases hwk : w = n + k
            · subst hwk
              simp only [Function.update_self, evalTag]
              cases hval : wpl p l (n + k)
              · rfl
              · exact absurd ⟨l, p, hp, hval⟩ hact
            · rw [Function.update_of_ne hwk]; exact hex l p hp w (by omega)
  obtain ⟨hsz, hao, hrb, hbd, htr, hup, hex⟩ := hInv C.gates.length le_rfl
  set gs := (build C.gates.length).1
  set mp := (build C.gates.length).2
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have hge' : (C.wires (List.ofFn (edge p₀ l₀))).length ≤ C.output := by
      change (runW C.gates (List.ofFn (edge p₀ l₀))).length ≤ C.output
      rw [hrun_len, List.length_ofFn]
      omega
    have hf : circuitFun n C (edge p₀ l₀) = false := by
      change (C.wires (List.ofFn (edge p₀ l₀))).getD C.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge']
      rfl
    have ht := (hT l₀ p₀ hp₀).2.1
    rw [hf] at ht
    cases ht
  have hout_tag : ∃ o₁ : ℕ, mp C.output = Sum.inr o₁ ∧ o₁ < n + gs.length := by
    have hb := hbd C.output hout_lt
    cases hm : mp C.output with
    | inl b =>
      cases b
      · have he := hex l₀ p₀ hp₀ C.output hout_lt
        rw [hm] at he
        simp only [evalTag] at he
        have ht := (hT l₀ p₀ hp₀).2.1
        change wpl p₀ l₀ C.output = true at ht
        rw [ht] at he
        cases he
      · have h0 := htr C.output hout_lt hm
        rw [show w0 C.output = false from hw0_out] at h0
        cases h0
    | inr o₁ =>
      rw [hm] at hb
      exact ⟨o₁, rfl, hb⟩
  obtain ⟨o₁, ho₁_eq, ho₁_lt⟩ := hout_tag
  let C1 : Circuit := ⟨gs, o₁⟩
  have hC1_size : C1.size ≤ A.card := by
    have hfilt : (A.filter fun j => j.val < C.gates.length) = A := by
      ext j
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro _
      exact j.isLt
    rw [hfilt] at hsz
    exact hsz
  have hC1_ao2 : PEqualNP.TopForm.IsAO2 n C1 := by
    refine ⟨fun g hg => (hao g hg).1, ?_, fun g hg => (hao g hg).2⟩
    intro j hj i hi
    exact hrb j hj i hi
  have hC1_le : ∀ z : Fin n → Bool, circuitFun n C1 z = true → circuitFun n C z = true := by
    intro z hz
    have hev : evalTag (runW gs (List.ofFn z)) (mp C.output) = true := by
      rw [ho₁_eq]
      exact hz
    exact hup z C.output hout_lt hev
  have hC1_sound : ∀ z : Fin n → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun n C1 z = false := by
    intro z hz hno
    cases hv : circuitFun n C1 z with
    | false => rfl
    | true =>
      have hc := hC1_le z hv
      rw [hsound z hz hno] at hc
      cases hc
  have hC1_acc : ∀ l p, p ∈ T l → circuitFun n C1 (edge p l) = true := by
    intro l p hp
    have he := hex l p hp C.output hout_lt
    rw [ho₁_eq] at he
    change circuitFun n C1 (edge p l) = circuitFun n C (edge p l) at he
    rw [he]
    exact (hT l p hp).2.1
  have hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l') := by
    intro p p' l l' hpp hll h
    obtain ⟨h11, h21, h12, h22⟩ := h
    obtain ⟨lstar, _, huniq'⟩ := huniq p p' hpp
    exact hll ((huniq' l ⟨h11, h21⟩).trans (huniq' l' ⟨h12, h22⟩).symm)
  let ET : Finset (Fin N × Fin N) := Finset.univ.filter fun e => e.1 ∈ T e.2
  have hET_card : ∑ l : Fin N, (T l).card = ET.card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro l _
    rw [← Finset.card_filter]
    congr 1
    ext p
    simp
  rw [hET_card]
  suffices hgoal : ET.card ≤ 44 * C1.size from hgoal.trans (Nat.mul_le_mul_left 44 hC1_size)
  by_cases hq87 : 87 ≤ q
  · have hb1 := h1 N I C1 hfour hC1_ao2 (fun z hz hno => hC1_sound z (hz.trans (by omega)) hno)
    have hb2 := h2 q N I C1 hq hN hcol huniq hC1_ao2 hC1_sound
    have hb3 := h3 q N I C1 hq87 hN hcol huniq hC1_ao2 hC1_sound
    rw [Fintype.card_subtype] at hb1 hb2 hb3
    let Ey : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
      I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C1 n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true
    let Ex : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
      I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C1 n (fun i => decide (i < N)) e.1.val (N + e.2.val) = true
    let Ed : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
      I e.1 e.2 ∧ circuitFun n C1 (edge e.1 e.2) = true ∧
      PEqualNP.ReadK.lineSingle C1 n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      PEqualNP.ReadK.lineSingle C1 n (fun i => decide (i < N)) e.1.val (N + e.2.val) = false
    have hsub : ET ⊆ (Ey ∪ Ex) ∪ Ed := by
      intro e he
      have hmem : e.1 ∈ T e.2 := (Finset.mem_filter.mp he).2
      have hi : I e.1 e.2 := (hT e.2 e.1 hmem).1
      have hacc : circuitFun n C1 (edge e.1 e.2) = true := hC1_acc e.2 e.1 hmem
      simp only [Finset.mem_union, Ey, Ex, Ed, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hy : PEqualNP.ReadK.lineSingle C1 n (fun i => decide (N ≤ i)) e.1.val (N + e.2.val)
      · cases hx : PEqualNP.ReadK.lineSingle C1 n (fun i => decide (i < N)) e.1.val (N + e.2.val)
        · exact Or.inr ⟨hi, hacc, rfl, rfl⟩
        · exact Or.inl (Or.inr ⟨hi, rfl⟩)
      · exact Or.inl (Or.inl ⟨hi, rfl⟩)
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le (Ey ∪ Ex) Ed
    have hc3 := Finset.card_union_le Ey Ex
    change Ey.card ≤ 10 * C1.size at hb1
    change Ex.card ≤ 10 * C1.size at hb2
    change Ed.card ≤ 24 * C1.size at hb3
    omega
  · have hq86 : q ≤ 86 := by omega
    -- Cone-pruning input-wire count: |P_T| + |L_T| <= C1.size + 1
    let stepR : ℕ → ℕ → Prop := fun a b =>
      ∃ j : Fin C1.size, b = n + j.val ∧ a ∈ (C1.gates[j.val]'j.isLt).inputs
    let reach : ℕ → Prop := fun a => Relation.ReflTransGen stepR a C1.output
    have hreach_eval : ∀ z₁ z₂ : Fin n → Bool,
        (∀ i : Fin n, reach i.val → z₁ i = z₂ i) →
        ∀ w, reach w → (C1.wires (List.ofFn z₁)).getD w false = (C1.wires (List.ofFn z₂)).getD w false := by
      intro z₁ z₂ hag w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hrw
        by_cases hlt : w < n
        · have h1 := hrun_prefix_getD [] C1.gates (List.ofFn z₁) w (by simp; omega)
          have h2 := hrun_prefix_getD [] C1.gates (List.ofFn z₂) w (by simp; omega)
          change (runW C1.gates (List.ofFn z₁)).getD w false = (runW C1.gates (List.ofFn z₂)).getD w false
          rw [show C1.gates = [] ++ C1.gates from rfl, h1, h2, hrun_nil, hrun_nil]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
          exact hag ⟨w, hlt⟩ hrw
        · by_cases hltg : w < n + C1.gates.length
          · let k : ℕ := w - n
            have hk : k < C1.gates.length := by omega
            have hwk : w = n + k := by omega
            have hg1 := hrun_gate_getD C1.gates (List.ofFn z₁) k hk
            have hg2 := hrun_gate_getD C1.gates (List.ofFn z₂) k hk
            rw [List.length_ofFn] at hg1 hg2
            change (runW C1.gates (List.ofFn z₁)).getD w false = (runW C1.gates (List.ofFn z₂)).getD w false
            rw [hwk, hg1, hg2]
            congr 1
            apply List.map_congr_left
            intro i hi
            have hi_lt : i < n + k := by
              have hrb' := hC1_ao2.2.1 k hk i
              change i ∈ (C1.gates.getD k ⟨GateOp.or, []⟩).inputs → i < n + k at hrb'
              rw [List.getD_eq_getElem C1.gates _ hk] at hrb'
              exact hrb' hi
            have hri : reach i := Relation.ReflTransGen.head ⟨⟨k, hk⟩, rfl, hi⟩ (hwk ▸ hrw)
            have hlenk : (C1.gates.take k).length = k := List.length_take_of_le hk.le
            have hp1 := hrun_prefix_getD (C1.gates.take k) (C1.gates.drop k) (List.ofFn z₁) i
              (by simp [hlenk]; omega)
            have hp2 := hrun_prefix_getD (C1.gates.take k) (C1.gates.drop k) (List.ofFn z₂) i
              (by simp [hlenk]; omega)
            rw [List.take_append_drop] at hp1 hp2
            rw [← hp1, ← hp2]
            exact ih i (by omega) hri
          · have hge1 : (C1.wires (List.ofFn z₁)).length ≤ w := by
              change (runW C1.gates (List.ofFn z₁)).length ≤ w
              rw [hrun_len, List.length_ofFn]; omega
            have hge2 : (C1.wires (List.ofFn z₂)).length ≤ w := by
              change (runW C1.gates (List.ofFn z₂)).length ≤ w
              rw [hrun_len, List.length_ofFn]; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge1,
                List.getD_eq_getElem?_getD, List.getElem?_eq_none hge2]
    have hout_ge : n ≤ C1.output := by
      by_contra hlt
      push Not at hlt
      have hout_eval : ∀ z : Fin n → Bool, circuitFun n C1 z = z ⟨C1.output, hlt⟩ := by
        intro z
        have hpr := hrun_prefix_getD [] C1.gates (List.ofFn z) C1.output (by simp; omega)
        change (runW C1.gates (List.ofFn z)).getD C1.output false = _
        rw [show C1.gates = [] ++ C1.gates from rfl, hpr, hrun_nil]
        simp [List.getD_eq_getElem?_getD, hlt]
      by_cases hp : C1.output < N
      · let z : Fin n → Bool := fun k => decide (k = Fin.castAdd N ⟨C1.output, hp⟩)
        have h1 : circuitFun n C1 z = true := by
          rw [hout_eval]
          simp [z, Fin.ext_iff]
        have h0 : circuitFun n C1 z = false := by
          apply hC1_sound z
          · have hemp : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} = 0 := by
              rw [Fintype.card_eq_zero_iff]
              refine ⟨fun x => ?_⟩
              have hl := x.property
              simp only [z, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl
              omega
            omega
          · rintro ⟨p, l, _, _, hl⟩
            simp only [z, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl
            omega
        rw [h0] at h1
        cases h1
      · let l : Fin N := ⟨C1.output - N, by omega⟩
        let z : Fin n → Bool := fun k => decide (k = Fin.natAdd N l)
        have h1 : circuitFun n C1 z = true := by
          rw [hout_eval]
          simp only [z, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, l]
          omega
        have h0 : circuitFun n C1 z = false := by
          apply hC1_sound z
          · rw [Fintype.card_subtype]
            have hsub : Finset.univ.filter (fun l' : Fin N => z (Fin.natAdd N l') = true) ⊆ {l} := by
              intro l' hl'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, z, decide_eq_true_eq] at hl'
              have hv := congrArg Fin.val hl'
              simp only [Fin.val_natAdd] at hv
              exact Finset.mem_singleton.mpr (Fin.ext (by omega))
            exact (Finset.card_le_card hsub).trans (by simp; omega)
          · rintro ⟨p, _, _, hp', _⟩
            simp only [z, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp'
            omega
        rw [h0] at h1
        cases h1
    let R : Finset (Fin C1.size) := Finset.univ.filter fun j => reach (n + j.val)
    let Sread : Finset ℕ := R.biUnion fun j => (C1.gates[j.val]'j.isLt).inputs.toFinset
    have hSread_le : Sread.card ≤ 2 * R.card := by
      calc Sread.card ≤ ∑ j ∈ R, ((C1.gates[j.val]'j.isLt).inputs.toFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ j ∈ R, (C1.gates[j.val]'j.isLt).inputs.length :=
          Finset.sum_le_sum (fun j _ => List.toFinset_card_le _)
        _ = ∑ _j ∈ R, 2 := Finset.sum_congr rfl (fun j _ => hC1_ao2.2.2 _ (List.getElem_mem j.isLt))
        _ = 2 * R.card := by simp [Nat.mul_comm]
    have hreach_in_Sread : ∀ w, reach w → w ≠ C1.output → w ∈ Sread := by
      intro w hrw hne
      rcases Relation.ReflTransGen.cases_head hrw with rfl | ⟨u, ⟨j, rfl, hjw⟩, hru⟩
      · exact absurd rfl hne
      · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hru⟩, ?_⟩
        exact List.mem_toFinset.mpr hjw
    let PT : Finset (Fin N) := ET.image Prod.fst
    let LT : Finset (Fin N) := ET.image Prod.snd
    have hPT_sub : PT.image (fun p : Fin N => p.val) ⊆ Sread := by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      have hmem : e.1 ∈ T e.2 := (Finset.mem_filter.mp he).2
      have hreach_p : reach e.1.val := by
        by_contra hnr
        let z₂ : Fin n → Bool := fun k => decide (k = Fin.natAdd N e.2)
        have hag : ∀ i : Fin n, reach i.val → edge e.1 e.2 i = z₂ i := by
          intro i hri
          have hne : i ≠ Fin.castAdd N e.1 := by
            intro heq
            have hv := congrArg Fin.val heq
            simp only [Fin.val_castAdd] at hv
            exact hnr (hv ▸ hri)
          simp only [edge, z₂, hne, false_or]
        have heq := hreach_eval (edge e.1 e.2) z₂ hag C1.output Relation.ReflTransGen.refl
        have h1 : circuitFun n C1 (edge e.1 e.2) = true := hC1_acc e.2 e.1 hmem
        have h0 : circuitFun n C1 z₂ = false := by
          apply hC1_sound z₂
          · rw [Fintype.card_subtype]
            have hsub : Finset.univ.filter (fun l' : Fin N => z₂ (Fin.natAdd N l') = true) ⊆ {e.2} := by
              intro l' hl'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, z₂, decide_eq_true_eq] at hl'
              have hv := congrArg Fin.val hl'
              simp only [Fin.val_natAdd] at hv
              exact Finset.mem_singleton.mpr (Fin.ext (by omega))
            exact (Finset.card_le_card hsub).trans (by simp; omega)
          · rintro ⟨p', _, _, hp', _⟩
            simp only [z₂, decide_eq_true_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hp'
            omega
        change circuitFun n C1 (edge e.1 e.2) = circuitFun n C1 z₂ at heq
        rw [h1, h0] at heq
        cases heq
      exact hreach_in_Sread e.1.val hreach_p (by have := e.1.isLt; omega)
    have hLT_sub : LT.image (fun l : Fin N => N + l.val) ⊆ Sread := by
      intro w hw
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      have hmem : e.1 ∈ T e.2 := (Finset.mem_filter.mp he).2
      have hreach_l : reach (N + e.2.val) := by
        by_contra hnr
        let z₂ : Fin n → Bool := fun k => decide (k = Fin.castAdd N e.1)
        have hag : ∀ i : Fin n, reach i.val → edge e.1 e.2 i = z₂ i := by
          intro i hri
          have hne : i ≠ Fin.natAdd N e.2 := by
            intro heq
            have hv := congrArg Fin.val heq
            simp only [Fin.val_natAdd] at hv
            exact hnr (hv ▸ hri)
          simp only [edge, z₂, hne, or_false]
        have heq := hreach_eval (edge e.1 e.2) z₂ hag C1.output Relation.ReflTransGen.refl
        have h1 : circuitFun n C1 (edge e.1 e.2) = true := hC1_acc e.2 e.1 hmem
        have h0 : circuitFun n C1 z₂ = false := by
          apply hC1_sound z₂
          · rw [Fintype.card_subtype]
            have hemp : Finset.univ.filter (fun l' : Fin N => z₂ (Fin.natAdd N l') = true) = ∅ := by
              ext l'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
                z₂, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
              omega
            rw [hemp]; simp
          · rintro ⟨_, l', _, _, hl'⟩
            simp only [z₂, decide_eq_true_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at hl'
            omega
        change circuitFun n C1 (edge e.1 e.2) = circuitFun n C1 z₂ at heq
        rw [h1, h0] at heq
        cases heq
      exact hreach_in_Sread (N + e.2.val) hreach_l (by have := e.2.isLt; omega)
    let R' : Finset (Fin C1.size) := R.filter fun j => n + j.val ≠ C1.output
    have hR'_sub : R'.image (fun j : Fin C1.size => n + j.val) ⊆ Sread := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have hjm := Finset.mem_filter.mp hj
      have hreach_j : reach (n + j.val) := (Finset.mem_filter.mp hjm.1).2
      exact hreach_in_Sread (n + j.val) hreach_j hjm.2
    have hC1_out_lt : C1.output < n + C1.size := ho₁_lt
    have hout_mem_R : (⟨C1.output - n, by omega⟩ : Fin C1.size) ∈ R := by
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      have heq : n + (C1.output - n) = C1.output := by omega
      rw [heq]
    have hR'_card : R'.card + 1 = R.card := by
      have herase : R' = R.erase ⟨C1.output - n, by omega⟩ := by
        ext j
        simp only [R', Finset.mem_filter, Finset.mem_erase, ne_eq, Fin.ext_iff]
        constructor
        · rintro ⟨hj, hne⟩
          exact ⟨by omega, hj⟩
        · rintro ⟨hne, hj⟩
          exact ⟨hj, by omega⟩
      rw [herase, Finset.card_erase_add_one hout_mem_R]
    let SP := PT.image (fun p : Fin N => p.val)
    let SL := LT.image (fun l : Fin N => N + l.val)
    let SG := R'.image (fun j : Fin C1.size => n + j.val)
    have hdisj_PL : Disjoint SP SL := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw1
      obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hw2
      have := p.isLt
      omega
    have hdisj_PLG : Disjoint (SP ∪ SL) SG := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw2
      rcases Finset.mem_union.mp hw1 with h | h
      · obtain ⟨p, _, heq⟩ := Finset.mem_image.mp h
        have := p.isLt; omega
      · obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h
        have := l.isLt; omega
    have hsum_le : PT.card + LT.card + R'.card ≤ Sread.card := by
      have hSP : SP.card = PT.card := Finset.card_image_of_injective _ (fun _ _ h => Fin.ext h)
      have hSL : SL.card = LT.card := Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))
      have hSG : SG.card = R'.card := Finset.card_image_of_injective _ (fun _ _ h => Fin.ext (by omega))
      have hsubU : (SP ∪ SL) ∪ SG ⊆ Sread :=
        Finset.union_subset (Finset.union_subset hPT_sub hLT_sub) hR'_sub
      have hc := Finset.card_le_card hsubU
      rw [Finset.card_union_of_disjoint hdisj_PLG, Finset.card_union_of_disjoint hdisj_PL,
        hSP, hSL, hSG] at hc
      exact hc
    have hR_le : R.card ≤ C1.size := by
      calc R.card ≤ (Finset.univ : Finset (Fin C1.size)).card := Finset.card_le_univ _
        _ = C1.size := Fintype.card_fin _
    have hPL_le : PT.card + LT.card ≤ C1.size + 1 := by omega
    -- Bound |ET| using line degree = q + 1 and point degree = q + 1
    have hET_sub : ET ⊆ PT ×ˢ LT := by
      intro e he
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
    have hET_le_prod : ET.card ≤ PT.card * LT.card := by
      simpa [Finset.card_product] using Finset.card_le_card hET_sub
    have hET_le_L : ET.card ≤ LT.card * (q + 1) := by
      have hsubL : ET ⊆ LT.biUnion (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
        intro e he
        refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image_of_mem _ he, ?_⟩
        exact Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hT e.2 e.1 (Finset.mem_filter.mp he).2).1⟩, rfl⟩
      calc ET.card ≤ ∑ l ∈ LT, ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card :=
            (Finset.card_le_card hsubL).trans Finset.card_biUnion_le
        _ ≤ ∑ l ∈ LT, (Finset.univ.filter (fun p : Fin N => I p l)).card :=
            Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = ∑ _l ∈ LT, (q + 1) := Finset.sum_congr rfl (fun l _ => by simpa [Fintype.card_subtype] using hcol l)
        _ = LT.card * (q + 1) := by simp
    have hpt_deg : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q + 1 := by
      intro p
      let Lp := Finset.univ.filter fun l : Fin N => I p l
      have hpart : (Finset.univ.erase p : Finset (Fin N)) =
          Lp.biUnion (fun l => (Finset.univ.filter fun p' : Fin N => I p' l).erase p) := by
        ext p'
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, Lp,
          Finset.mem_filter, true_and]
        constructor
        · intro hne
          obtain ⟨l, ⟨hp1, hp2⟩, _⟩ := huniq p p' hne.symm
          exact ⟨l, hp1, hne, hp2⟩
        · rintro ⟨_, _, hne, _⟩
          exact hne
      have hdisj : Set.PairwiseDisjoint (↑Lp) (fun l => (Finset.univ.filter fun p' : Fin N => I p' l).erase p) := by
        intro l₁ hl₁ l₂ hl₂ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro p' hp1 hp2
        have h1 := Finset.mem_erase.mp hp1
        have h2 := Finset.mem_erase.mp hp2
        have h1' := (Finset.mem_filter.mp h1.2).2
        have h2' := (Finset.mem_filter.mp h2.2).2
        have hl1' := (Finset.mem_filter.mp hl₁).2
        have hl2' := (Finset.mem_filter.mp hl₂).2
        exact hfour p p' l₁ l₂ h1.1.symm hne ⟨hl1', h1', hl2', h2'⟩
      have hcard_eq := congrArg Finset.card hpart
      rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin,
        Finset.card_biUnion hdisj] at hcard_eq
      have hsum_q : ∑ l ∈ Lp, ((Finset.univ.filter fun p' : Fin N => I p' l).erase p).card = Lp.card * q := by
        have heach : ∀ l ∈ Lp, ((Finset.univ.filter fun p' : Fin N => I p' l).erase p).card = q := by
          intro l hl
          have hmem : p ∈ Finset.univ.filter (fun p' : Fin N => I p' l) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
          rw [Finset.card_erase_of_mem hmem]
          have hc := hcol l
          rw [Fintype.card_subtype] at hc
          omega
        rw [Finset.sum_congr rfl heach]
        simp
      rw [hsum_q] at hcard_eq
      have hN1 : N - 1 = (q + 1) * q := by
        rw [hN, Nat.add_sub_cancel]
        ring
      rw [hN1] at hcard_eq
      exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) hcard_eq.symm
    have hET_le_P : ET.card ≤ PT.card * (q + 1) := by
      have hsubP : ET ⊆ PT.biUnion (fun p => (Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l))) := by
        intro e he
        refine Finset.mem_biUnion.mpr ⟨e.1, Finset.mem_image_of_mem _ he, ?_⟩
        exact Finset.mem_image.mpr ⟨e.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hT e.2 e.1 (Finset.mem_filter.mp he).2).1⟩, rfl⟩
      calc ET.card ≤ ∑ p ∈ PT, ((Finset.univ.filter (fun l : Fin N => I p l)).image (fun l => (p, l))).card :=
            (Finset.card_le_card hsubP).trans Finset.card_biUnion_le
        _ ≤ ∑ p ∈ PT, (Finset.univ.filter (fun l : Fin N => I p l)).card :=
            Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = ∑ _p ∈ PT, (q + 1) := Finset.sum_congr rfl (fun p _ => hpt_deg p)
        _ = PT.card * (q + 1) := by simp
    have hPT_pos : 1 ≤ PT.card := Finset.one_le_card.mpr ⟨p₀, Finset.mem_image.mpr ⟨(p₀, l₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp₀⟩, rfl⟩⟩
    have hLT_pos : 1 ≤ LT.card := Finset.one_le_card.mpr ⟨l₀, Finset.mem_image.mpr ⟨(p₀, l₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp₀⟩, rfl⟩⟩
    have hC1_pos : 1 ≤ C1.size := by omega
    by_cases hcase : PT.card ≤ LT.card
    · by_cases hsmall : LT.card ≤ 44
      · nlinarith
      · by_cases hpa : PT.card ≤ 43
        · nlinarith
        · nlinarith
    · by_cases hsmall : PT.card ≤ 44
      · nlinarith
      · by_cases hla : LT.card ≤ 43
        · nlinarith
        · nlinarith
