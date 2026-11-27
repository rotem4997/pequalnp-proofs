import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Read the prescribed first gate as a tenth input. A shortest witness
-- then ends with a binary operation on two different readers or a NOT.
theorem PEqualNP.Outside.R_meta_1671_2 :
    (∀ (tail : List Gate) (a b : ℕ), FanInTwo ⟨tail, 0⟩ → tail.length ≤ 13 →
      a < b → b < 10 + tail.length →
      (fun x : Fin 9 → Bool =>
        (Circuit.mk tail a).eval (List.ofFn x ++ [(x 0 && x 6)]) &&
        (Circuit.mk tail b).eval (List.ofFn x ++ [(x 0 && x 6)])) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ (tail : List Gate) (a b : ℕ), FanInTwo ⟨tail, 0⟩ → tail.length ≤ 13 →
      a < b → b < 10 + tail.length →
      (fun x : Fin 9 → Bool =>
        (Circuit.mk tail a).eval (List.ofFn x ++ [(x 0 && x 6)]) ||
        (Circuit.mk tail b).eval (List.ofFn x ++ [(x 0 && x 6)])) ≠ (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
    (∀ (tail : List Gate) (a : ℕ), FanInTwo ⟨tail, 0⟩ → tail.length ≤ 13 →
      (fun x : Fin 9 → Bool => (Circuit.mk tail a).eval (List.ofFn x ++ [(x 0 && x 6)])) ≠
      (fun x : Fin 9 → Bool => !((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  classical
  intro noAnd noOr noNot C givenFan givenFirst givenRun
  by_contra! givenSize
  let f := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  change (fun x : Fin 9 → Bool => C.eval (List.ofFn x)) = f at givenRun
  have ffalse : f (fun _ => false) = false := rfl
  have ftrue : f (fun _ => true) = true := rfl
  have fsingle : ∀ i : Fin 9, f (fun j => decide (j = i)) = false := by decide
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wiresLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  have keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have hi' : i < (step w g).length := by simp [step]; omega
      rw [List.foldl_cons, ih _ hi']
      have ha : i < (step w g).length := hi'
      rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hi]
      exact List.getElem_append_left hi
  have evalStep (gs : List Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (Circuit.mk gs o).eval (List.ofFn x) =
        (gs.foldl step (List.ofFn x)).getD o false := rfl
  have endWire (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by omega)]
    simp
  have noInput (i : Fin 9) :
      ¬ ∀ x : Fin 9 → Bool, x i = f x := by
    intro h
    simpa [fsingle i] using h (fun j => decide (j = i))
  let good (D : Circuit) : Prop :=
    FanInTwo D ∧
    (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 0 && x 6)) ∧
    (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = f x)
  let existsAt (k : ℕ) : Prop := ∃ D : Circuit, D.size ≤ k ∧ good D
  have given : existsAt 15 := by
    refine ⟨C, by omega, givenFan, givenFirst, ?_⟩
    intro x
    exact congrFun givenRun x
  obtain ⟨s, ⟨⟨gs,o⟩, hsize, hfan, hfirst, hrun⟩, hmin⟩ :=
    Nat.findX (show ∃ k, existsAt k from ⟨15, given⟩)
  have hs15 : s ≤ 15 := by
    by_contra! h
    exact hmin 15 h given
  change gs.length ≤ s at hsize
  have oLow : 9 ≤ o := by
    by_contra! ho
    let i : Fin 9 := ⟨o,ho⟩
    apply noInput i
    intro x
    have h := hrun x
    rw [evalStep, keepWire _ _ _ (by simpa using ho),
      List.getD_eq_getElem _ _ (by simpa using ho)] at h
    simpa only [List.getElem_ofFn] using h
  have oHigh : o < 9 + gs.length := by
    by_contra! ho
    have h := hrun (fun _ => true)
    rw [evalStep, List.getD_eq_default _ _ (by
      rw [wiresLen, List.length_ofFn]; exact ho), ftrue] at h
    cases h
  let k := o - 9 + 1
  have hk : k ≤ gs.length := by dsimp [k]; omega
  have takeLen : (gs.take k).length = k := by simp [List.length_take, hk]
  have pref : existsAt k := by
    refine ⟨⟨gs.take k,o⟩, ?_, fun g hg => hfan g (List.mem_of_mem_take hg), ?_, ?_⟩
    · change (gs.take k).length ≤ k
      rw [takeLen]
    · intro x
      have h := hfirst x
      change (gs.foldl step (List.ofFn x)).getD 9 false = (x 0 && x 6) at h
      rw [← List.take_append_drop k gs, List.foldl_append,
        keepWire _ _ _ (by
          rw [wiresLen, List.length_ofFn, takeLen]
          dsimp [k]
          omega)] at h
      exact h
    intro x
    have h := hrun x
    rw [evalStep, ← List.take_append_drop k gs, List.foldl_append,
      keepWire _ _ _ (by
        rw [wiresLen, List.length_ofFn, takeLen]
        dsimp [k]
        omega)] at h
    rw [evalStep]
    exact h
  have hsK : s ≤ k := by
    by_contra! h
    exact hmin k h pref
  rcases List.eq_nil_or_concat' gs with hnil | ⟨pre,g,rfl⟩
  · simp [hnil] at oHigh
    omega
  have olen : o = 9 + pre.length := by
    simp only [List.length_append, List.length_singleton] at hsize oHigh hk
    dsimp [k] at hsK
    omega
  subst o
  have sz : pre.length < s := by simpa using hsize
  have cap : pre.length ≤ 14 := by omega
  have prefixFan (o : ℕ) : FanInTwo ⟨pre,o⟩ :=
    fun g hg => hfan g (List.mem_append_left _ hg)
  let v (i : ℕ) (x : Fin 9 → Bool) : Bool := (Circuit.mk pre i).eval (List.ofFn x)
  have preNonempty : pre ≠ [] := by
    intro hn
    let probe : Fin 9 → Bool := fun j => decide (j = 5 ∨ j = 8)
    have h1 := hfirst probe
    have h2 := hrun probe
    have id : 9 + pre.length = 9 := by simp [hn]
    simp only [id] at h2
    rw [evalStep] at h2
    change ((pre ++ [g]).foldl step (List.ofFn probe)).getD 9 false =
      ((probe 0 && probe 6)) at h1
    rw [h1] at h2
    have differs : ((probe 0 && probe 6)) ≠ f probe := by decide
    exact differs h2
  have preFirst (x : Fin 9 → Bool) :
      (pre.foldl step (List.ofFn x)).getD 9 false = (x 0 && x 6) := by
    have h := hfirst x
    change ((pre ++ [g]).foldl step (List.ofFn x)).getD 9 false = (x 0 && x 6) at h
    have hlen : 0 < pre.length := List.length_pos_iff_ne_nil.mpr preNonempty
    rw [List.foldl_append, keepWire _ _ _ (by rw [wiresLen, List.length_ofFn]; omega)] at h
    exact h
  have noRead (i : ℕ) : ¬ ∀ x, v i x = f x := by
    intro hv
    exact hmin pre.length sz ⟨⟨pre,i⟩, le_rfl, prefixFan i, preFirst, hv⟩
  obtain ⟨first, tail, hpre⟩ := List.exists_cons_of_ne_nil preNonempty
  have tailFan : FanInTwo ⟨tail, 0⟩ := by
    intro g' hg'
    exact prefixFan 0 g' (by rw [hpre]; exact List.mem_cons_of_mem _ hg')
  have tailCap : tail.length ≤ 13 := by
    rw [hpre, List.length_cons] at cap
    omega
  have readerBound (i : ℕ) (hi : i < 9 + pre.length) : i < 10 + tail.length := by
    rw [hpre, List.length_cons] at hi
    omega
  have peel (i : ℕ) (x : Fin 9 → Bool) :
      v i x = (Circuit.mk tail i).eval (List.ofFn x ++ [(x 0 && x 6)]) := by
    have h := preFirst x
    rw [hpre, List.foldl_cons, keepWire _ _ _ (by
      simp only [step, List.length_append, List.length_singleton, List.length_ofFn]
      omega)] at h
    have hs : step (List.ofFn x) first = List.ofFn x ++ [(x 0 && x 6)] := by
      let value := first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false)
      have hv := endWire (List.ofFn x) value
      rw [List.length_ofFn] at hv
      change (List.ofFn x ++ [value]).getD 9 false = (x 0 && x 6) at h
      rw [hv] at h
      exact congrArg (fun bit => List.ofFn x ++ [bit]) h
    unfold v
    rw [evalStep, hpre, List.foldl_cons, hs]
    rfl
  have missing (i : ℕ) (hi : 9 + pre.length ≤ i) (x : Fin 9 → Bool) :
      v i x = false := by
    unfold v
    rw [evalStep, List.getD_eq_default _ _ (by rw [wiresLen,List.length_ofFn]; exact hi)]
  have gateValue (x : Fin 9 → Bool) :
      g.op.eval (g.inputs.map (fun i => v i x)) = f x := by
    have h := hrun x
    rw [evalStep, List.foldl_append] at h
    change
      ((pre.foldl step (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => (pre.foldl step (List.ofFn x)).getD i false)]).getD
          (9 + pre.length) false = f x at h
    have hw : (pre.foldl step (List.ofFn x)).length = 9 + pre.length := by
      rw [wiresLen, List.length_ofFn]
    rw [← hw, endWire] at h
    exact h
  obtain ⟨op, arity⟩ := hfan g (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
  have binary (op' : GateOp) (hv : op' = .and ∨ op' = .or)
      (hvalue : ∀ x, op'.eval (g.inputs.map (fun i => v i x)) = f x) : False := by
    rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, L⟩⟩⟩
    · rcases hv with rfl | rfl
      · have h := hvalue (fun _ => false)
        rw [hi] at h
        change true = f (fun _ => false) at h
        rw [ffalse] at h
        cases h
      · have h := hvalue (fun _ => true)
        rw [hi] at h
        change false = f (fun _ => true) at h
        rw [ftrue] at h
        cases h
    · apply noRead a
      intro x
      rcases hv with rfl | rfl
      · have h := hvalue x
        rw [hi] at h
        change (v a x && true) = f x at h
        simpa only [Bool.and_true] using h
      · have h := hvalue x
        rw [hi] at h
        change (v a x || false) = f x at h
        simpa only [Bool.or_false] using h
    · rcases hv with rfl | rfl
      · have hAB (x) : (v a x && v b x) = f x := by
          have h := hvalue x
          rw [hi] at h
          change (v a x && (v b x && true)) = f x at h
          simpa only [Bool.and_true] using h
        have ha : a < 9 + pre.length := by
          by_contra! h
          simpa [missing _ h, ftrue] using hAB (fun _ => true)
        have hb : b < 9 + pre.length := by
          by_contra! h
          simpa [missing _ h, ftrue] using hAB (fun _ => true)
        have hn : a ≠ b := by
          rintro rfl
          exact noRead a (fun x => by simpa using hAB x)
        rcases lt_or_gt_of_ne hn with h | h
        · apply noAnd tail a b tailFan tailCap h (readerBound b hb)
          funext x
          rw [← peel a x, ← peel b x]
          exact hAB x
        · apply noAnd tail b a tailFan tailCap h (readerBound a ha)
          funext x
          rw [← peel b x, ← peel a x, Bool.and_comm]
          exact hAB x
      · have hAB (x) : (v a x || v b x) = f x := by
          have h := hvalue x
          rw [hi] at h
          change (v a x || (v b x || false)) = f x at h
          simpa only [Bool.or_false] using h
        have ha : a < 9 + pre.length := by
          by_contra! h
          exact noRead b (fun x => by simpa [missing _ h x] using hAB x)
        have hb : b < 9 + pre.length := by
          by_contra! h
          exact noRead a (fun x => by simpa [missing _ h x] using hAB x)
        have hn : a ≠ b := by
          rintro rfl
          exact noRead a (fun x => by simpa using hAB x)
        rcases lt_or_gt_of_ne hn with h | h
        · apply noOr tail a b tailFan tailCap h (readerBound b hb)
          funext x
          rw [← peel a x, ← peel b x]
          exact hAB x
        · apply noOr tail b a tailFan tailCap h (readerBound a ha)
          funext x
          rw [← peel b x, ← peel a x, Bool.or_comm]
          exact hAB x
    · rw [hi] at arity
      simp at arity
  rcases op with h | h | h
  · exact binary g.op (.inl h) gateValue
  · exact binary g.op (.inr h) gateValue
  · cases hi : g.inputs with
    | nil =>
      have hbad := gateValue (fun _ => false)
      rw [h, hi] at hbad
      change true = f (fun _ => false) at hbad
      rw [ffalse] at hbad
      cases hbad
    | cons a rest =>
      apply noNot tail a tailFan tailCap
      funext x
      rw [← peel a x]
      have hv := gateValue x
      rw [h, hi] at hv
      change (!v a x) = f x at hv
      change v a x = !f x
      simpa only [Bool.not_not] using congrArg Bool.not hv
