import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each list entry holds three 20-bit tests, least significant test and input bit first.
-- Positive rows are ordered by point and line index. Negative masks are sorted numerically.
-- To enumerate the latter, choose a subset of the five points and its compatible lines.
-- Use all compatible lines if the points are collinear, or intersect them with a point pencil.
-- Project these inputs and retain the inclusion-maximal distinct masks.
theorem PEqualNP.Outside.R_meta_2712_1
    (finiteSynthesis :
      let table := fun (t : List ℕ) (j : ℕ) (i : Fin 20) => (t.getD (j / 3) 0).testBit (20 * (j % 3) + i.val)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 23 ∧
        (∀ j : Fin 20, circuitFun 20 C (table [882706627014164513,72567803150337,74801153180674,72062818869837956,720866211591618600,720875007625924616,8606712336] j) = true) ∧
        ∀ j : Fin 44, circuitFun 20 C (table [4665232155738143,13518504604999695,725368754528096277,730724029253162005,866973350870287389,875963053248350355,884986756446568478,903000063497490454,954792603833647132,1012212425860929682,1041183516279060867,1062218301194542225,1078371242023506996,1142983005070916482,1099479117384] j) = false)
    (negativeCover :
      let pin (x : Fin 26 → Bool) (i : Fin 20) :=
        if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else
          if i.val < 14 then i.val+8 else i.val+9))
        else (decide (i.val ≠ 18) && (x 16 || x 18)) ||
          (decide (i.val ≠ 17) && (x 19 || x 23))
      let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
      ∀ x : Fin 26 → Bool,
        (∀ p l, x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) = true → ¬ I p l) →
        ((∃ l, ∀ p, x (Fin.castAdd 13 p) = true → I p l) ∨
          ∃ p, ∀ l, x (Fin.natAdd 13 l) = true → I p l) →
        ∃ j : Fin 44, ∀ i, pin x i = true →
          ((([4665232155738143,13518504604999695,725368754528096277,730724029253162005,866973350870287389,875963053248350355,884986756446568478,903000063497490454,954792603833647132,1012212425860929682,1041183516279060867,1062218301194542225,1078371242023506996,1142983005070916482,1099479117384] : List ℕ).getD (j.val / 3) 0).testBit (20 * (j.val % 3) + i.val)) = true) :
    have x1 : (Fin (26 : ℕ) → Bool) → Fin (20 : ℕ) → Bool := fun (x1 : Fin (26 : ℕ) → Bool) (x2 : Fin (20 : ℕ)) => if ↑x2 < (17 : ℕ) then x1 (Fin.ofNat (26 : ℕ) (if ↑x2 < (5 : ℕ) then ↑x2 else if ↑x2 < (14 : ℕ) then ↑x2 + (8 : ℕ) else ↑x2 + (9 : ℕ))) else Decidable.decide (↑x2 ≠ (18 : ℕ)) && (x1 (16 : Fin (26 : ℕ)) || x1 (18 : Fin (26 : ℕ))) || Decidable.decide (↑x2 ≠ (17 : ℕ)) && (x1 (19 : Fin (26 : ℕ)) || x1 (23 : Fin (26 : ℕ))); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], x2 = x3 + x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (23 : ℕ) ∧ (∀ (x4 x5 : Fin (13 : ℕ)), ↑x4 < (5 : ℕ) → x2 x4 x5 → PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x4 ∨ x8 = Fin.natAdd (13 : ℕ) x5)) = Bool.true) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (∀ (x5 x6 : Fin (13 : ℕ)), x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true → x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true → ¬x2 x5 x6) → ((∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x4 (Fin.castAdd (13 : ℕ) x7) = Bool.true → x2 x7 x6) ∨ ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x4 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x2 x6 x7) → PEqualNP.MetaComplexity.circuitFun (20 : ℕ) x3 (x1 x4) = Bool.false := by
  dsimp only
  let pin (x : Fin 26 → Bool) (i : Fin 20) :=
    if i.val < 17 then x (Fin.ofNat 26 (if i.val < 5 then i.val else
      if i.val < 14 then i.val+8 else i.val+9))
    else (decide (i.val ≠ 18) && (x 16 || x 18)) ||
      (decide (i.val ≠ 17) && (x 19 || x 23))
  let I := fun p l : Fin 13 => ∃ d ∈ ([0,1,3,9] : List (Fin 13)), p = l+d
  let yes : Fin 20 → Fin 20 → Bool := fun j i =>
    ((([882706627014164513,72567803150337,74801153180674,72062818869837956,720866211591618600,720875007625924616,8606712336] : List ℕ).getD (j.val / 3) 0).testBit (20 * (j.val % 3) + i.val))
  let no : Fin 44 → Fin 20 → Bool := fun j i =>
    ((([4665232155738143,13518504604999695,725368754528096277,730724029253162005,866973350870287389,875963053248350355,884986756446568478,903000063497490454,954792603833647132,1012212425860929682,1041183516279060867,1062218301194542225,1078371242023506996,1142983005070916482,1099479117384] : List ℕ).getD (j.val / 3) 0).testBit (20 * (j.val % 3) + i.val))
  have yesRows : ∀ p l : Fin 13, p.val < 5 → I p l →
      ∃ j : Fin 20, ∀ i, pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l)) i =
        yes j i := by decide +kernel
  obtain ⟨C,hm,hs,hyes,hno⟩ := finiteSynthesis
  have monotoneEval (x y : Fin 20 → Bool) (hxy : ∀ i, x i = true → y i = true) :
      circuitFun 20 C x = true → circuitFun 20 C y = true := by
    let V (w : List Bool) (i : ℕ) := w.getD i false
    let R (w z : List Bool) := w.length = z.length ∧ ∀ i, V w i = true → V z i = true
    have step (g : Gate) (hg : g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        g.op.eval (g.inputs.map (V w)) = true →
        g.op.eval (g.inputs.map (V z)) = true := by
      have hops := (hm g hg).1
      change g.op = .and ∨ g.op = .or at hops
      rcases hops with h | h <;> rw [h]
      · change (g.inputs.map (V w)).all id = true → (g.inputs.map (V z)).all id = true
        simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun all i hi => hr.2 i (all i hi)
      · change (g.inputs.map (V w)).any id = true → (g.inputs.map (V z)).any id = true
        simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,hval⟩
        exact ⟨i,hi,hr.2 i hval⟩
    let evalStep (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map (V w))]
    have run (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ C.gates) (w z : List Bool) (hr : R w z) :
        R (gs.foldl evalStep w) (gs.foldl evalStep z) := by
      induction gs generalizing w z with
      | nil => exact hr
      | cons g gs ih =>
        apply ih (fun h hh => hsub h (List.mem_cons_of_mem _ hh))
        refine ⟨by simp only [evalStep,List.length_append,List.length_singleton,hr.1], ?_⟩
        intro i
        change (w ++ [_]).getD i false = true → (z ++ [_]).getD i false = true
        by_cases h : i < w.length
        · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (by simpa only [← hr.1] using h)]
          exact hr.2 i
        · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by rw [← hr.1]; omega),← hr.1]
          cases i-w.length with
          | zero => exact step g (hsub g List.mem_cons_self) w z hr
          | succ k => simp
    have hi : R (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp only [List.length_ofFn], ?_⟩
      intro i
      by_cases h : i < 20
      · change (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true
        have hx : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact h
        have hy : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact h
        rw [List.getD_eq_getElem _ _ hx,List.getD_eq_getElem _ _ hy,
          List.getElem_ofFn,List.getElem_ofFn]
        exact hxy ⟨i,h⟩
      · change (List.ofFn x).getD i false = true → _
        rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]
        intro hf; cases hf
    exact (run C.gates (fun _ h => h) _ _ hi).2 C.output
  refine ⟨C,hm,hs,?_,?_⟩
  · intro p l hp hpl
    obtain ⟨j,h⟩ := yesRows p l hp hpl
    change circuitFun 20 C (pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l))) = true
    rw [funext h]
    exact hyes j
  · intro x hind hdeg
    obtain ⟨j,hj⟩ := negativeCover x hind hdeg
    change circuitFun 20 C (pin x) = false
    cases h : circuitFun 20 C (pin x) with
    | false => rfl
    | true =>
      have contra := monotoneEval (pin x) (no j) hj h
      exact Bool.noConfusion (contra.symm.trans (hno j))
