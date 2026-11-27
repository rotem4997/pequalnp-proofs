import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Lines 5 and 11 meet exactly the same one of the five points. One OR merges
-- them. The other supplied unions still see their original inputs.
-- The 44-row geometric cover and monotonicity argument follow PR 5230.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2712_41
    (finiteSynthesis :
      let table := fun (t : List ℕ) (j : ℕ) (i : Fin 18) => (t.getD (j / 3) 0).testBit (18 * (j % 3) + i.val)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 22 ∧
        (∀ j : Fin 19, circuitFun 18 C (table [2748787982369,5497575964738,35253127217284,282575027307024,2252083281805314,13581476935368968,204801] j) = true) ∧
        ∀ j : Fin 40, circuitFun 18 C (table [150839794335775,422694713036815,10135127528966407,10573287142082581,13723262631478299,14075863940142091,14216052114924046,14708841020862478,15160192239357073,15517191257677852,16327395760634660,16879903704853650,17843491875054616,262112] j) = false)
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
  let no : Fin 44 → Fin 20 → Bool := fun j i =>
    ((([4665232155738143,13518504604999695,725368754528096277,730724029253162005,866973350870287389,875963053248350355,884986756446568478,903000063497490454,954792603833647132,1012212425860929682,1041183516279060867,1062218301194542225,1078371242023506996,1142983005070916482,1099479117384] : List ℕ).getD (j.val / 3) 0).testBit (20 * (j.val % 3) + i.val))
  let sel (i : Fin 18) : Fin 20 := Fin.ofNat 20
    (if i.val < 10 then i.val else if i.val < 16 then i.val+1 else i.val+2)
  let compress (v : Fin 20 → Bool) (i : Fin 18) :=
    if i.val = 14 then v 10 || v 15 else v (sel i)
  let tbl (ns : List ℕ) (j : ℕ) (i : Fin 18) := (ns.getD (j / 3) 0).testBit (18 * (j % 3) + i.val)
  let good (j : Fin 19) := tbl [2748787982369,5497575964738,35253127217284,282575027307024,2252083281805314,13581476935368968,204801] j.val
  let bad (j : Fin 40) := tbl [150839794335775,422694713036815,10135127528966407,10573287142082581,13723262631478299,14075863940142091,14216052114924046,14708841020862478,15160192239357073,15517191257677852,16327395760634660,16879903704853650,17843491875054616,262112] j.val
  have posMap : ∀ p l : Fin 13, p.val < 5 → I p l → ∃ j : Fin 19, ∀ i,
      good j i = true → compress (pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l))) i = true := by
    decide +kernel
  have negMap : ∀ j : Fin 44, ∃ k : Fin 40, ∀ i,
      compress (no j) i = true → bad k i = true := by decide +kernel
  obtain ⟨C,hm,hs,hyes,hno⟩ := finiteSynthesis

  have monotoneEval (x y : Fin 18 → Bool) (hxy : ∀ i, x i = true → y i = true) :
      circuitFun 18 C x = true → circuitFun 18 C y = true := by
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
      by_cases h : i < 18
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
  let idx (i : ℕ) := if h : i < 18 then
    if i = 14 then 20 else (sel ⟨i,h⟩).val else i+3
  let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map idx⟩
  let liftC : Circuit := ⟨⟨.or,[10,15]⟩ :: C.gates.map rename,idx C.output⟩
  have legal : Monotone2 liftC := by
    intro g hg
    change g ∈ _ :: _ at hg
    simp only [List.mem_cons,List.mem_map] at hg
    rcases hg with rfl | ⟨v,hv,rfl⟩
    · exact ⟨by simp, Nat.le_refl 2⟩
    · exact ⟨(hm v hv).1, by simpa [rename] using (hm v hv).2⟩
  have small : liftC.size ≤ 23 := by
    change C.gates.length ≤ 22 at hs
    change (_ :: _).length ≤ 23
    simp only [List.length_cons,List.length_map]
    omega
  have simulate (u : Fin 20 → Bool) : circuitFun 20 liftC u = circuitFun 18 C (compress u) := by
    let val := u 10 || u 15
    let X := List.ofFn (compress u)
    let Y := List.ofFn u ++ [val]
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have readU (i : Fin 20) : (List.ofFn u).getD i.val false = u i := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt]
      rfl
    have init : step (List.ofFn u) ⟨.or,[10,15]⟩ = Y := by
      change _ ++ [((List.ofFn u).getD 10 false || ((List.ofFn u).getD 15 false || false))] = _
      rw [show (List.ofFn u).getD 10 false = u 10 from readU 10,
          show (List.ofFn u).getD 15 false = u 15 from readU 15,Bool.or_false]
    have reads (t : List Bool) (i : ℕ) : (X ++ t).getD i false = (Y ++ t).getD (idx i) false := by
      by_cases hi : i < 18
      · rw [List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa only [X,List.length_ofFn] using hi)]
        change ((List.ofFn (compress u))[i]?).getD false = _
        rw [List.getElem?_ofFn,dite_eq_left hi]
        by_cases hm : i = 14
        · subst i
          change val = (((List.ofFn u) ++ [val]) ++ t).getD 20 false
          rw [List.append_assoc,List.getD_append_right _ _ _ _ (by simp)]
          simp
        · have ilt := (sel ⟨i,hi⟩).isLt
          simp only [idx,dite_eq_left hi,ite_eq_right hm,Y,List.append_assoc]
          rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using ilt),readU]
          simp [compress,hm]
      · simp only [idx,dite_eq_right hi]
        rw [List.getD_append_right _ _ _ _ (by simp only [X,List.length_ofFn]; omega),
            List.getD_append_right _ _ _ _ (by simp only [Y,List.length_append,List.length_ofFn,List.length_singleton]; omega)]
        simp only [X,Y,List.length_append,List.length_ofFn,List.length_singleton]
        congr 1
    have run (gs : List Gate) (t : List Bool) : ∃ v : List Bool,
        gs.foldl step (X ++ t) = X ++ v ∧ (gs.map rename).foldl step (Y ++ t) = Y ++ v := by
      induction gs generalizing t with
      | nil => exact ⟨t,rfl,rfl⟩
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map (fun i => (X ++ t).getD i false))
        have eqb : g.op.eval (g.inputs.map (fun i => (X ++ t).getD i false)) =
            (rename g).op.eval ((rename g).inputs.map (fun i => (Y ++ t).getD i false)) := by
          congr 1
          simp only [rename,List.map_map]
          apply List.map_congr_left
          intro i _
          exact reads t i
        obtain ⟨v,hx,hy⟩ := ih (t ++ [bit])
        refine ⟨v,?_,?_⟩
        · simpa only [List.foldl_cons,step,List.append_assoc,bit] using hx
        · change (gs.map rename).foldl step ((Y ++ t) ++ [_]) = _
          rw [← eqb,List.append_assoc]
          exact hy
    obtain ⟨v,hx,hy⟩ := run C.gates []
    simp only [List.append_nil] at hx hy
    change ((C.gates.map rename).foldl step (step (List.ofFn u) _)).getD (idx C.output) false =
      (C.gates.foldl step X).getD C.output false
    rw [init,hx,hy]
    exact (reads v C.output).symm
  refine ⟨liftC,legal,small,?_,?_⟩
  · intro p l hp hpl
    obtain ⟨j,h⟩ := posMap p l hp hpl
    change circuitFun 20 liftC (pin (fun z => decide (z = Fin.castAdd 13 p ∨ z = Fin.natAdd 13 l))) = true
    rw [simulate]
    exact monotoneEval (good j) _ h (hyes j)
  · intro x hind hdeg
    obtain ⟨j,hj⟩ := negativeCover x hind hdeg
    obtain ⟨k,hk⟩ := negMap j
    have hcomp (i : Fin 18) : compress (pin x) i = true → compress (no j) i = true := by
      by_cases he : i.val = 14
      · simp only [compress,ite_eq_left he,Bool.or_eq_true]
        exact fun h => h.imp (hj 10) (hj 15)
      · simpa only [compress,ite_eq_right he] using hj (sel i)
    change circuitFun 20 liftC (pin x) = false
    rw [simulate]
    cases h : circuitFun 18 C (compress (pin x)) with
    | false => rfl
    | true =>
      have con := monotoneEval _ (bad k) (fun i hb => hk i (hcomp i hb)) h
      exact Bool.noConfusion (con.symm.trans (hno k))
