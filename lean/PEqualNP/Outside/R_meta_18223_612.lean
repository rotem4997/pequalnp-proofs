import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_18223_612
    (rowZero : ∀ C : Circuit, IsAO2 26 C →
      (∀ x : Fin 26 → Bool, x 0 = false → (C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) → 59 ≤ C.size)
    (lineZero : ∀ C : Circuit, IsAO2 26 C →
      (∀ x : Fin 26 → Bool, x 13 = false → (C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)) → 59 ≤ C.size) :
    (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (∀ (x5 : Fin (26 : ℕ) → Bool), x5 x2 = Bool.false → (x3.eval (List.ofFn x5) = Bool.true ↔ x1 x5)) → (59 : ℕ) ≤ x3.size) := by
  dsimp only
  intro v C hC hCompute
  let incidence (x : Fin 26 → Bool) := ∃ p l : Fin 13,
    p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let shift (k : Fin 13) : Fin 26 → Fin 26 := fun v =>
    Fin.addCases (motive := fun _ => Fin 26)
      (fun i : Fin 13 => Fin.castAdd 13 (i + k))
      (fun i : Fin 13 => Fin.natAdd 13 (i + k)) v
  have shiftRow (k i : Fin 13) :
      shift k (Fin.castAdd 13 i) = Fin.castAdd 13 (i + k) := by simp [shift]
  have shiftLine (k i : Fin 13) :
      shift k (Fin.natAdd 13 i) = Fin.natAdd 13 (i + k) := by
    exact Fin.addCases_right i
  have edgeShift : ∀ k p l : Fin 13,
      p + k ∈ singerLines3 (l + k) ↔ p ∈ singerLines3 l := by decide +kernel
  have incidenceShift (k : Fin 13) (x : Fin 26 → Bool) :
      incidence (fun i => x (shift k i)) ↔ incidence x := by
    constructor
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨p + k, l + k, (edgeShift k p l).2 h, by simpa only [shiftRow] using hp,
        by simpa only [shiftLine] using hl⟩
    · rintro ⟨p, l, h, hp, hl⟩
      refine ⟨p - k, l - k, (edgeShift k (p - k) (l - k)).1 (by simpa using h), ?_, ?_⟩
      · simpa only [shiftRow, sub_add_cancel] using hp
      · simpa only [shiftLine, sub_add_cancel] using hl
  let wire (k : Fin 13) (i : ℕ) := if h : i < 26 then (shift k ⟨i, h⟩).val else i
  have wireBound (k : Fin 13) (i j : ℕ) (hi : i < 26 + j) : wire k i < 26 + j := by
    by_cases h : i < 26
    · exact (show wire k i < 26 by simp [wire, h]).trans_le (by omega)
    · simpa [wire, h] using hi
  let renameGate (k : Fin 13) (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire k)⟩
  let D (k : Fin 13) : Circuit := ⟨C.gates.map (renameGate k), wire k C.output⟩
  have dSize (k : Fin 13) : (D k).size = C.size := by
    change (C.gates.map (renameGate k)).length = C.gates.length
    exact List.length_map _
  have dModel (k : Fin 13) : IsAO2 26 (D k) := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      change g ∈ C.gates.map (renameGate k) at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact hC.1 g' hg'
    · intro j hj i hi
      change j < (C.gates.map (renameGate k)).length at hj
      simp only [List.length_map] at hj
      change i ∈ ((C.gates.map (renameGate k)).getD j ⟨.or, []⟩).inputs at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some, renameGate] at hi
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
      apply wireBound
      apply hC.2.1 j hj i'
      change i' ∈ (C.gates.getD j ⟨.or, []⟩).inputs
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hi'
    · intro g hg
      change g ∈ C.gates.map (renameGate k) at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using hC.2.2 g' hg'
  have dEval (k : Fin 13) (x : Fin 26 → Bool) :
      (D k).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (shift k i))) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wireAgree (gates : List Gate) (xs ys : List Bool)
        (hlen : xs.length = ys.length) (hn : 26 ≤ xs.length)
        (hbits : ∀ i, xs.getD (wire k i) false = ys.getD i false) :
        ∀ i, (List.foldl step xs (gates.map (renameGate k))).getD (wire k i) false =
          (List.foldl step ys gates).getD i false := by
      induction gates generalizing xs ys with
      | nil => exact hbits
      | cons g gates ih =>
        have hv : (renameGate k g).op.eval ((renameGate k g).inputs.map fun i => xs.getD i false) =
            g.op.eval (g.inputs.map fun i => ys.getD i false) := by
          simp only [renameGate, List.map_map]
          congr 1
          exact List.map_congr_left (fun i _ => hbits i)
        simp only [List.map_cons, List.foldl_cons]
        apply ih
        · simp [step, hlen]
        · simp [step]; omega
        · intro i
          dsimp only [step]
          rw [hv]
          by_cases h : i < 26
          · have hw : wire k i < xs.length := by
              have hh : wire k i < 26 := by simp [wire, h]
              omega
            have hy : i < ys.length := by omega
            rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hy]
            exact hbits i
          · have hw : wire k i = i := by simp [wire, h]
            rw [hw]
            by_cases hi : i < ys.length
            · rw [List.getD_append _ _ _ _ (hlen.symm ▸ hi), List.getD_append _ _ _ _ hi]
              simpa only [hw] using hbits i
            · rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega), hlen]
    unfold D Circuit.eval Circuit.wires
    exact wireAgree C.gates _ _ (by simp) (by simp) (by
      intro i
      by_cases h : i < 26
      · have hs := (shift k ⟨i, h⟩).isLt
        simp only [wire, dite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          dite_eq_left hs, Option.getD_some]
      · simp only [wire, dite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          Option.getD_none]) C.output
  have bound (z : Fin 26) (k : Fin 13) (hk : shift k v = z)
      (hzero : ∀ C : Circuit, IsAO2 26 C →
        (∀ x : Fin 26 → Bool, x z = false → (C.eval (List.ofFn x) = true ↔ incidence x)) →
        59 ≤ C.size) : 59 ≤ C.size := by
    have h := hzero (D k) (dModel k) (by
      intro x hx
      rw [dEval]
      exact (hCompute _ (by simpa [hk] using hx)).trans (incidenceShift k x))
    rwa [dSize] at h
  by_cases hv : v.val < 13
  · let p : Fin 13 := ⟨v.val, hv⟩
    have hp : v = Fin.castAdd 13 p := Fin.ext rfl
    apply bound 0 (-p) _ rowZero
    rw [hp, shiftRow, add_neg_cancel]
    rfl
  · let l : Fin 13 := ⟨v.val - 13, by have := v.isLt; omega⟩
    have hl : v = Fin.natAdd 13 l := Fin.ext (by change v.val = 13 + (v.val - 13); omega)
    apply bound 13 (-l) _ lineZero
    rw [hl, shiftLine, add_neg_cancel]
    rfl
