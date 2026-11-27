import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_18796_416
    (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (59 : ℕ) ≤ x1.size)
    (encoding : ∀ p l : Fin 13, p ∈ singerLines3 l ↔
      p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x3 (0 : Fin (26 : ℕ)) = Bool.false → (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true)) → (59 : ℕ) ≤ x1.size := by
  intro C hC hCorrect
  let evaluate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let advance (w : List Bool) (g : Gate) := w ++ [evaluate w g]
  let legal (n : ℕ) (g : Gate) :=
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n ∧ b < n
  let valid (n : ℕ) (gs : List Gate) := ∀ j g, gs[j]? = some g → legal (n + j) g
  letI : DecidableEq GateOp := gateOpDecEq
  have andNeOr : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h
  let patch (live : List Bool) (g : Gate) : Gate :=
    let a := g.inputs.getD 0 0
    let b := g.inputs.getD 1 0
    if live.getD a false then
      if live.getD b false then g
      else if g.op = .or then ⟨.or, [a, a]⟩ else ⟨.or, [0, 0]⟩
    else if live.getD b false then
      if g.op = .or then ⟨.or, [b, b]⟩ else ⟨.or, [0, 0]⟩
    else ⟨.or, [0, 0]⟩
  let push (state : List Bool × List Gate) (g : Gate) :=
    (advance state.1 g, state.2 ++ [patch state.1 g])
  let build (live : List Bool) (gs : List Gate) := (gs.foldl push (live, [])).2
  have pushPrefix (gs : List Gate) (live : List Bool) (prior : List Gate) :
      (gs.foldl push (live, prior)).2 = prior ++ build live gs := by
    induction gs generalizing live prior with
    | nil => simp [build]
    | cons g gs ih =>
      change (gs.foldl push (advance live g, prior ++ [patch live g])).2 =
        prior ++ (gs.foldl push (advance live g, [patch live g])).2
      rw [ih, ih, List.append_assoc]
  have buildCons (g : Gate) (gs : List Gate) (live : List Bool) :
      build live (g :: gs) = patch live g :: build (advance live g) gs := by
    change (gs.foldl push (advance live g, [patch live g])).2 = _
    exact pushPrefix gs (advance live g) [patch live g]
  have advanceLen (w : List Bool) (g : Gate) : (advance w g).length = w.length + 1 := by
    simp [advance]
  have buildLen (gs : List Gate) (live : List Bool) : (build live gs).length = gs.length := by
    induction gs generalizing live with
    | nil => rfl
    | cons g gs ih => rw [buildCons]; simp [ih]
  have patchLegal (n : ℕ) (hn : 0 < n) (live : List Bool) (g : Gate) (hg : legal n g) :
      legal n (patch live g) := by
    have hgCopy := hg
    obtain ⟨hop, a, b, hab, ha, hb⟩ := hgCopy
    have dummy : legal n (⟨.or, [0, 0]⟩ : Gate) := ⟨Or.inr rfl, 0, 0, rfl, hn, hn⟩
    have copy (w : ℕ) (hw : w < n) : legal n (⟨.or, [w, w]⟩ : Gate) :=
      ⟨Or.inr rfl, w, w, rfl, hw, hw⟩
    cases wa : live.getD a false <;> cases wb : live.getD b false <;>
      rcases hop with h | h <;> simp only [patch, hab, List.getD_cons_zero, List.getD_cons_succ, wa, wb, h, andNeOr, Bool.false_eq_true,
        ↓reduceIte] <;> first | exact dummy | exact copy a ha | exact copy b hb | exact hg
  have buildValid (gs : List Gate) (live : List Bool) (hn : 0 < live.length)
      (h : valid live.length gs) : valid live.length (build live gs) := by
    induction gs generalizing live with
    | nil => intro j g hj; simp [build] at hj
    | cons g gs ih =>
      have tail : valid (advance live g).length gs := by
        intro j g' hj
        rw [advanceLen, Nat.add_assoc, Nat.add_comm 1 j]
        exact h (j + 1) g' hj
      intro j g' hj
      rw [buildCons] at hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst g'
        exact patchLegal _ (by simpa using hn) live g (h 0 g rfl)
      | succ j =>
        have hp := ih (advance live g) (by rw [advanceLen]; omega) tail j g' hj
        simpa only [advanceLen, Nat.add_assoc, Nat.add_comm 1 j] using hp
  have readAppend (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases same : i = w.length
    · subst i; simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right same]
      by_cases before : i < w.length
      · exact List.getD_append _ _ _ _ before
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  let agree (live old new : List Bool) := ∀ i,
    old.getD i false = (live.getD i false && new.getD i false)
  have evalAnd (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    cases a <;> cases b <;> rfl
  have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    cases a <;> cases b <;> rfl
  have sameGate (live old new : List Bool) (g : Gate) (hg : legal live.length g)
      (h : agree live old new) :
      evaluate old g = (evaluate live g && evaluate new (patch live g)) := by
    obtain ⟨hop, a, b, hab, _, _⟩ := hg
    rcases g with ⟨op, inputs⟩
    change inputs = [a, b] at hab
    subst inputs
    change op = .and ∨ op = .or at hop
    have ha := h a
    have hb := h b
    rcases hop with rfl | rfl <;>
      cases wa : live.getD a false <;> cases wb : live.getD b false <;>
      simp only [evaluate, patch, List.map_cons, List.map_nil, evalAnd, evalOr,
        List.getD_cons_zero, List.getD_cons_succ, ha, hb, wa, wb, andNeOr, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_and,
        Bool.true_and, Bool.and_true, Bool.false_or, Bool.or_false, Bool.or_self]
  have agreeStep (live old new : List Bool) (g : Gate) (hg : legal live.length g)
      (ho : old.length = live.length) (hn : new.length = live.length)
      (h : agree live old new) :
      agree (advance live g) (advance old g) (advance new (patch live g)) := by
    intro i
    change (old ++ [_]).getD i false = ((live ++ [_]).getD i false && (new ++ [_]).getD i false)
    simp only [readAppend, ho, hn]
    by_cases hi : i = live.length
    · simpa only [ite_eq_left hi] using sameGate live old new g hg h
    · simpa only [ite_eq_right hi] using h i
  have agreeBuild (gs : List Gate) (live old new : List Bool) (hv : valid live.length gs)
      (ho : old.length = live.length) (hn : new.length = live.length) (h : agree live old new) :
      agree (gs.foldl advance live) (gs.foldl advance old)
        ((build live gs).foldl advance new) := by
    induction gs generalizing live old new with
    | nil => exact h
    | cons g gs ih =>
      rw [buildCons]
      simp only [List.foldl_cons]
      apply ih
      · intro j g' hj
        rw [advanceLen, Nat.add_assoc, Nat.add_comm 1 j]
        exact hv (j + 1) g' hj
      · simp only [advanceLen, ho]
      · simp only [advanceLen, hn]
      · exact agreeStep live old new g (hv 0 g rfl) ho hn h
  have gateEq (gs : List Gate) (j : ℕ) (g : Gate) (h : gs[j]? = some g) :
      gs.getD j ⟨.or, []⟩ = g := by
    simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]
  have original : valid 26 C.gates := by
    intro j g hg
    have hmem := List.mem_of_getElem? hg
    have hj : j < C.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
    have hb := hC.2.1 j hj
    change ∀ i ∈ (C.gates.getD j ⟨.or, []⟩).inputs, i < 26 + j at hb
    rw [gateEq _ _ _ hg] at hb
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 g hmem)
    exact ⟨hC.1 g hmem, a, b, hab, hb a (by simp [hab]), hb b (by simp [hab])⟩
  let top : Fin 26 → Bool := fun i => decide (i ≠ 0)
  let fixed (x : Fin 26 → Bool) : Fin 26 → Bool := fun i => if i = 0 then false else x i
  let D : Circuit := ⟨build (List.ofFn top) C.gates, C.output⟩
  have dSize : D.size = C.size := buildLen _ _
  have dValid : valid 26 D.gates := by
    apply buildValid C.gates (List.ofFn top) (by simp)
    simpa only [List.length_ofFn] using original
  have dModel : IsAO2 26 D := by
    have atPos (j : ℕ) (hj : j < D.gates.length) : legal (26 + j) (gateAt D j) := by
      have hg := List.getElem?_eq_getElem hj
      have h := dValid j D.gates[j] hg
      change legal (26 + j) (D.gates.getD j ⟨.or, []⟩)
      rwa [gateEq _ _ _ hg]
    have onMember (g : Gate) (hg : g ∈ D.gates) : ∃ n, legal n g := by
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
      refine ⟨26+i, ?_⟩
      have h := atPos i hi
      change legal (26 + i) (D.gates.getD i ⟨.or, []⟩) at h
      rwa [gateEq _ _ _ (List.getElem?_eq_getElem hi), hgi] at h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨_, h⟩ := onMember g hg
      exact h.1
    · intro j hj i hi
      obtain ⟨_, a, b, hab, ha, hb⟩ := atPos j hj
      simp only [hab, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    · intro g hg
      obtain ⟨_, _, a, b, hab, _, _⟩ := onMember g hg
      simp [hab]
  have topTrue : C.eval (List.ofFn top) = true := by
    apply (hCorrect top (by decide)).2
    exact ⟨1, 1, by decide, by decide, by decide⟩
  have dEval (x : Fin 26 → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn (fixed x)) := by
    have initial : agree (List.ofFn top) (List.ofFn (fixed x)) (List.ofFn x) := by
      intro i
      by_cases hi : i < 26
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
        by_cases h : (⟨i, hi⟩ : Fin 26) = 0 <;> simp [fixed, top, h]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hi,
          Option.getD_none, Bool.false_and]
    have outcome := agreeBuild C.gates (List.ofFn top) (List.ofFn (fixed x)) (List.ofFn x)
      (by simpa only [List.length_ofFn] using original)
      (by simp only [List.length_ofFn]) (by simp only [List.length_ofFn]) initial C.output
    change C.eval (List.ofFn (fixed x)) = (C.eval (List.ofFn top) && D.eval (List.ofFn x)) at outcome
    rw [topTrue, Bool.true_and] at outcome
    exact outcome.symm
  have pzero : ∀ p : Fin 13, Fin.castAdd 13 p = (0 : Fin 26) ↔ p = 0 := by decide
  have lnonzero : ∀ l : Fin 13, Fin.natAdd 13 l ≠ (0 : Fin 26) := by decide
  rw [← dSize]
  apply lower D dModel
  intro x
  rw [dEval, hCorrect _ (by simp [fixed])]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    have pNe : p ≠ 0 := by
      intro h
      simp [fixed, (pzero p).2 h] at hx
    exact ⟨p, l, (encoding p l).1 hp, pNe,
      by simpa [fixed, mt (pzero p).1 pNe] using hx,
      by simpa only [fixed, ite_eq_right (lnonzero l)] using hy⟩
  · rintro ⟨p, l, hp, pNe, hx, hy⟩
    exact ⟨p, l, (encoding p l).2 hp,
      by simpa [fixed, mt (pzero p).1 pNe] using hx,
      by simpa only [fixed, ite_eq_right (lnonzero l)] using hy⟩
