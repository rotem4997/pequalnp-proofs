import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With at least two NOT gates, the ten-input suffix has at most twelve binary gates.
-- With at most one NOT gate, its single read of the extra input must survive absorption.
set_option maxHeartbeats 900000 in
theorem PEqualNP.Outside.R_meta_3089_1
    (many :
      let target := (fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      ∀ C : Circuit, FanInTwo C → C.size = 14 →
        2 ≤ C.gates.countP (fun g => g.op.eval [false]) →
        (∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0]) ≠ target x) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ target x)
    (few :
      let target := (fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
      ∀ C : Circuit,
        let reads := C.output :: C.gates.flatMap Gate.inputs
        FanInTwo C → C.size = 14 →
        C.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
        (C.output ≤ 10 + C.size ∧ ∀ g ∈ C.gates, ∀ a ∈ g.inputs, a ≤ 10 + C.size) →
        (∀ a < 10 + C.size, a ∈ reads) →
        9 + (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length +
          (∑ a ∈ Finset.range (10 + C.size), (reads.count a - 1)) ≤ C.size →
        reads.count 9 = 1 →
        C.output ≠ 9 →
        (∀ g ∈ C.gates, 9 ∈ g.inputs →
          ¬ ∃ p : Fin 9, ∀ (x : Fin 9 → Bool) (wire : ℕ → Bool),
            (∀ i : Fin 9, wire i.val = x i) →
            g.op.eval (g.inputs.map (fun a => if a = 9 then x 0 || x 3 else wire a)) =
            g.op.eval (g.inputs.map (fun a => if a = 9 then x p else wire a))) →
        (∀ p : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x p]) ≠ target x) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ target x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) = (1 : ℕ) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  intro rawTarget C fan size ranges live budget once different
  by_cases high : 2 ≤ C.gates.countP (fun g => g.op.eval [false])
  · exact many C fan size high (different 0)
  by_contra! correct
  have outputNotAnchor : C.output ≠ 9 := by
    intro h
    let x : Fin 9 → Bool := fun i => decide (i = 0)
    have run : ∀ (gs : List Gate) (w : List Bool), 9 < w.length →
        (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)]) w).getD 9 false =
          w.getD 9 false := by
      intro gs
      induction gs with
      | nil => simp
      | cons g gs ih =>
        intro w hw
        rw [List.foldl_cons, ih _ (by simp; omega)]
        exact List.getD_append _ _ _ _ hw
    have hc := correct x
    change (C.gates.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)])
      (List.ofFn x ++ [x 0 || x 3])).getD C.output false = rawTarget x at hc
    rw [h, run _ _ (by simp)] at hc
    have wrong : ((List.ofFn x ++ [x 0 || x 3]).getD 9 false) ≠ rawTarget x := by decide +kernel
    exact wrong hc
  have substantive (g : Gate) (hg : g ∈ C.gates) (hread : 9 ∈ g.inputs) : ¬ ∃ p : Fin 9,
      ∀ (x : Fin 9 → Bool) (wire : ℕ → Bool), (∀ i : Fin 9, wire i.val = x i) →
        g.op.eval (g.inputs.map (fun a => if a = 9 then x 0 || x 3 else wire a)) =
        g.op.eval (g.inputs.map (fun a => if a = 9 then x p else wire a)) := by
    rintro ⟨p, neutral⟩
    obtain ⟨before, after, split⟩ := List.append_of_mem hg
    have onceAgain : (C.gates.flatMap Gate.inputs).count 9 = 1 := by
      simpa [List.count_cons, outputNotAnchor] using once
    rw [split, List.flatMap_append, List.flatMap_cons, List.count_append, List.count_append] at onceAgain
    have gateReads : 0 < g.inputs.count 9 := List.count_pos_iff.mpr hread
    have beforeReads : ∀ g' ∈ before, 9 ∉ g'.inputs := by
      intro g' hg' h9
      have present : 9 ∈ before.flatMap Gate.inputs := List.mem_flatMap.mpr ⟨g', hg', h9⟩
      have positive : 0 < (before.flatMap Gate.inputs).count 9 := List.count_pos_iff.mpr present
      omega
    have afterReads : ∀ g' ∈ after, 9 ∉ g'.inputs := by
      intro g' hg' h9
      have present : 9 ∈ after.flatMap Gate.inputs := List.mem_flatMap.mpr ⟨g', hg', h9⟩
      have positive : 0 < (after.flatMap Gate.inputs).count 9 := List.count_pos_iff.mpr present
      omega
    obtain ⟨x, mismatch⟩ := different p
    let step (w : List Bool) (gate : Gate) :=
      w ++ [gate.op.eval (gate.inputs.map fun a => w.getD a false)]
    let related (a b : List Bool) : Prop :=
      a.length = b.length ∧ 9 < a.length ∧ ∀ i, i ≠ 9 → a.getD i false = b.getD i false
    have appendEq (a b : List Bool) (v : Bool) (same : related a b) :
        related (a ++ [v]) (b ++ [v]) := by
      refine ⟨by simp [same.1], by have h := same.2.1; simp; omega, ?_⟩
      intro i notAnchor
      rcases lt_trichotomy i a.length with h | h | h
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by simpa only [same.1] using h)]
        exact same.2.2 i notAnchor
      · have hb : i = b.length := h.trans same.1
        rw [List.getD_append_right _ _ _ _ h.ge, List.getD_append_right _ _ _ _ hb.ge]
        simp [h, hb, same.1]
      · have hb : b.length < i := same.1 ▸ h
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have foldEq (gs : List Gate) (ok : ∀ gate ∈ gs, 9 ∉ gate.inputs)
        (a b : List Bool) (same : related a b) : related (gs.foldl step a) (gs.foldl step b) := by
      induction gs generalizing a b with
      | nil => exact same
      | cons gate gs ih =>
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun other hother => ok other (List.mem_cons_of_mem _ hother))
        have equal : gate.inputs.map (fun i => a.getD i false) = gate.inputs.map (fun i => b.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact same.2.2 i (fun eq => ok gate List.mem_cons_self (eq ▸ hi))
        unfold step
        rw [equal]
        exact appendEq _ _ _ same
    have retain (gs : List Gate) (a : List Bool) (i : ℕ) (hi : i < a.length) :
        (gs.foldl step a).getD i false = a.getD i false := by
      induction gs generalizing a with
      | nil => rfl
      | cons gate gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    let a := List.ofFn x ++ [x 0 || x 3]
    let b := List.ofFn x ++ [x p]
    have init : related a b := by
      refine ⟨by simp [a,b], by simp [a], ?_⟩
      intro i ne
      by_cases early : i < 9
      · exact (List.getD_append _ _ _ _ (by simpa using early)).trans
          (List.getD_append _ _ _ _ (by simpa using early)).symm
      · exact (List.getD_eq_default _ _ (by simp [a]; omega)).trans
          (List.getD_eq_default _ _ (by simp [b]; omega)).symm
    let wa := before.foldl step a
    let wb := before.foldl step b
    have relatedBefore : related wa wb := foldEq before beforeReads a b init
    have za : wa.getD 9 false = (x 0 || x 3) := by
      rw [retain _ _ _ (by simp [a])]
      simp [a, List.getD_eq_getElem?_getD]
    have zb : wb.getD 9 false = x p := by
      rw [retain _ _ _ (by simp [b])]
      simp [b, List.getD_eq_getElem?_getD]
    have raw (i : Fin 9) : wa.getD i.val false = x i := by
      have bound : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
      rw [retain _ _ _ (by have h := i.isLt; simp [a]; omega)]
      change (List.ofFn x ++ [x 0 || x 3]).getD i.val false = x i
      rw [List.getD_append _ _ _ _ bound, List.getD_eq_getElem _ _ bound]
      simp only [List.getElem_ofFn]
    have eqA : g.inputs.map (fun i => wa.getD i false) =
        g.inputs.map (fun i => if i = 9 then x 0 || x 3 else wa.getD i false) := by
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · simpa only [h] using za
      · rfl
    have eqB : g.inputs.map (fun i => wb.getD i false) =
        g.inputs.map (fun i => if i = 9 then x p else wa.getD i false) := by
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · simpa only [h] using zb
      · exact (relatedBefore.2.2 i h).symm
    have gateEq : g.op.eval (g.inputs.map (fun i => wa.getD i false)) =
        g.op.eval (g.inputs.map (fun i => wb.getD i false)) := by
      rw [eqA, eqB]
      exact neutral x (fun i => wa.getD i false) raw
    have next : related (step wa g) (step wb g) := by
      unfold step
      rw [gateEq]
      exact appendEq _ _ _ relatedBefore
    have sameOutput := (foldEq after afterReads _ _ next).2.2 C.output outputNotAnchor
    have equalEval : C.eval a = C.eval b := by
      change (C.gates.foldl step a).getD C.output false = (C.gates.foldl step b).getD C.output false
      rw [split, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
      exact sameOutput
    rw [← correct x] at mismatch
    exact mismatch equalEval.symm
  have targetEq : rawTarget = (fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) := by decide +kernel
  obtain ⟨x, mismatch⟩ := few C fan size (by omega) ranges live budget once outputNotAnchor substantive
    (by simpa only [targetEq] using different)
  exact mismatch (by simpa only [targetEq] using correct x)
