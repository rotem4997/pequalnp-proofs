import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_18798_417
    (pointZero : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false → (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) → (59 : ℕ) ≤ x1.size)
    (polarity : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ -l ∈ singerLines3 (-p)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x3 (13 : Fin (26 : ℕ)) = Bool.false → (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) → (59 : ℕ) ≤ x1.size := by
  intro C hC hCompute
  let incidence (x : Fin 26 → Bool) := ∃ p l : Fin 13,
    p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let dual (v : Fin 26) : Fin 26 :=
    Fin.addCases (motive := fun _ => Fin 26)
      (fun p : Fin 13 => Fin.natAdd 13 (-p))
      (fun l : Fin 13 => Fin.castAdd 13 (-l)) v
  have dualPoint (i : Fin 13) : dual (Fin.castAdd 13 i) = Fin.natAdd 13 (-i) := by
    exact Fin.addCases_left i
  have dualLine (i : Fin 13) : dual (Fin.natAdd 13 i) = Fin.castAdd 13 (-i) := by
    exact Fin.addCases_right i
  have dualZero : dual 13 = 0 := by
    change dual (Fin.natAdd 13 (0 : Fin 13)) = 0
    rw [dualLine, neg_zero]
    rfl
  have incidenceDual (x : Fin 26 → Bool) : incidence (fun i => x (dual i)) ↔ incidence x := by
    constructor
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨-l, -p, (polarity p l).1 h, by simpa only [dualLine] using hl,
        by simpa only [dualPoint] using hp⟩
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨-l, -p, (polarity p l).1 h, by simpa only [dualPoint, neg_neg] using hl,
        by simpa only [dualLine, neg_neg] using hp⟩
  let wire (i : ℕ) := if h : i < 26 then (dual ⟨i, h⟩).val else i
  have wireBound (i j : ℕ) (hi : i < 26 + j) : wire i < 26 + j := by
    by_cases h : i < 26
    · exact (show wire i < 26 by simp [wire, h]).trans_le (by omega)
    · simpa [wire, h] using hi
  let renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map (wire)⟩
  let D : Circuit := ⟨C.gates.map renameGate, wire C.output⟩
  have dSize : D.size = C.size := by
    change (C.gates.map renameGate).length = C.gates.length
    exact List.length_map _
  have dModel : IsAO2 26 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      change g ∈ C.gates.map renameGate at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact hC.1 g' hg'
    · intro j hj i hi
      change j < (C.gates.map renameGate).length at hj
      simp only [List.length_map] at hj
      change i ∈ ((C.gates.map renameGate).getD j ⟨.or, []⟩).inputs at hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
        Option.map_some, Option.getD_some, renameGate] at hi
      obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
      apply wireBound
      apply hC.2.1 j hj i'
      change i' ∈ (C.gates.getD j ⟨.or, []⟩).inputs
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hi'
    · intro g hg
      change g ∈ C.gates.map renameGate at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using hC.2.2 g' hg'
  have dEval (x : Fin 26 → Bool) :
      D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (dual i))) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wireAgree (gates : List Gate) (xs ys : List Bool)
        (hlen : xs.length = ys.length) (hn : 26 ≤ xs.length)
        (hbits : ∀ i, xs.getD (wire i) false = ys.getD i false) :
        ∀ i, (List.foldl step xs (gates.map renameGate)).getD (wire i) false =
          (List.foldl step ys gates).getD i false := by
      induction gates generalizing xs ys with
      | nil => exact hbits
      | cons g gates ih =>
        have hv : (renameGate g).op.eval ((renameGate g).inputs.map fun i => xs.getD i false) =
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
          · have hw : wire i < xs.length := by
              have hh : wire i < 26 := by simp [wire, h]
              omega
            have hy : i < ys.length := by omega
            rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hy]
            exact hbits i
          · have hw : wire i = i := by simp [wire, h]
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
      · have hs := (dual ⟨i, h⟩).isLt
        simp only [wire, dite_eq_left h, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          dite_eq_left hs, Option.getD_some]
      · simp only [wire, dite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
          Option.getD_none]) C.output
  rw [← dSize]
  apply pointZero D dModel
  intro x hx
  rw [dEval]
  exact (hCompute _ (by simpa only [dualZero] using hx)).trans (incidenceDual x)
