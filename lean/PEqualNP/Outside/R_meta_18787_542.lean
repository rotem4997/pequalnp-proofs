import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_18787_542
    (exactBinary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (25 : ℕ) x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size)
    (someEdge : ∃ (p : Fin 12) (l : Fin 13),
      p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size := by
  intro C hC hCorrect
  let evalGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let advance (w : List Bool) (g : Gate) := w ++ [evalGate w g]
  let simple (gs : List Gate) := ∀ g ∈ gs,
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
  let legal (n : ℕ) (g : Gate) :=
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < n ∧ b < n
  let valid (n : ℕ) (gs : List Gate) := ∀ j g, gs[j]? = some g → legal (n + j) g
  let live (lo hi : List Bool) (i : ℕ) := !lo.getD i false && hi.getD i false
  let copy (i : ℕ) : Gate := ⟨.or, [i, i]⟩
  let patch (lo hi : List Bool) (g : Gate) : Gate :=
    let a := g.inputs.getD 0 hi.length
    let b := g.inputs.getD 1 hi.length
    if live lo hi a then
      if live lo hi b then g else copy a
    else if live lo hi b then copy b else copy 0
  let push (state : List Bool × List Bool × List Gate) (g : Gate) :=
    (advance state.1 g, advance state.2.1 g, state.2.2 ++ [patch state.1 state.2.1 g])
  let build (lo hi : List Bool) (gs : List Gate) := (gs.foldl push (lo, hi, [])).2.2
  have pushPrefix (gs : List Gate) (lo hi : List Bool) (prior : List Gate) :
      (gs.foldl push (lo, hi, prior)).2.2 = prior ++ build lo hi gs := by
    induction gs generalizing lo hi prior with
    | nil => simp [build]
    | cons g gs ih =>
      change (gs.foldl push (advance lo g, advance hi g, prior ++ [patch lo hi g])).2.2 =
        prior ++ (gs.foldl push (advance lo g, advance hi g, [patch lo hi g])).2.2
      rw [ih, ih, List.append_assoc]
  have buildCons (g : Gate) (gs : List Gate) (lo hi : List Bool) :
      build lo hi (g :: gs) = patch lo hi g :: build (advance lo g) (advance hi g) gs := by
    change (gs.foldl push (_, _, [patch lo hi g])).2.2 = _
    exact pushPrefix gs (advance lo g) (advance hi g) [patch lo hi g]
  have advanceLen (w : List Bool) (g : Gate) : (advance w g).length = w.length + 1 := by
    simp [advance]
  have buildLen (gs : List Gate) (lo hi : List Bool) : (build lo hi gs).length = gs.length := by
    induction gs generalizing lo hi with
    | nil => rfl
    | cons g gs ih => rw [buildCons]; simp [ih]
  have liveLt (lo hi : List Bool) (i : ℕ) (h : live lo hi i = true) : i < hi.length := by
    by_contra! hn
    simp only [live, List.getD_eq_default _ _ hn, Bool.and_false, Bool.false_eq_true] at h
  have patchLegal (lo hi : List Bool) (g : Gate) (hn : 0 < hi.length)
      (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) : legal hi.length (patch lo hi g) := by
    let a := g.inputs.getD 0 hi.length
    let b := g.inputs.getD 1 hi.length
    have copyLegal (i : ℕ) (h : i < hi.length) : legal hi.length (copy i) :=
      ⟨Or.inr rfl, i, i, rfl, h, h⟩
    change legal hi.length (if live lo hi a then (if live lo hi b then g else copy a)
        else if live lo hi b then copy b else copy 0)
    split
    · rename_i ha
      split
      · rename_i hb
        have hb' := liveLt _ _ _ hb
        have minLen : 2 ≤ g.inputs.length := by
          by_contra! hshort
          have hbEq : b = hi.length := List.getD_eq_default _ _ (by omega)
          omega
        have hab := List.length_eq_two.mp (by omega : g.inputs.length = 2)
        obtain ⟨u, v, huv⟩ := hab
        have ae : a = u := by simp only [a, huv, List.getD_cons_zero]
        have be : b = v := by simp only [b, huv, List.getD_cons_succ, List.getD_cons_zero]
        exact ⟨hop, u, v, huv, ae ▸ liveLt _ _ _ ha, be ▸ hb'⟩
      · exact copyLegal a (liveLt _ _ _ ha)
    · split
      · rename_i hb; exact copyLegal b (liveLt _ _ _ hb)
      · exact copyLegal 0 hn
  have buildValid (gs : List Gate) (lo hi : List Bool) (hn : 0 < hi.length)
      (h : simple gs) : valid hi.length (build lo hi gs) := by
    induction gs generalizing lo hi with
    | nil => intro j g hj; simp [build] at hj
    | cons g gs ih =>
      have tail : simple gs := fun g' hm => h g' (List.mem_cons_of_mem _ hm)
      intro j g' hj
      rw [buildCons] at hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst g'
        obtain ⟨ho, hlen⟩ := h g (by simp)
        exact patchLegal lo hi g hn ho hlen
      | succ j =>
        have hp := ih (advance lo g) (advance hi g) (by rw [advanceLen]; omega) tail j g' hj
        simpa only [advanceLen, Nat.add_assoc, Nat.add_comm 1 j] using hp
  have readAppend (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases same : i = w.length
    · subst i; simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right same]
      by_cases before : i < w.length
      · exact List.getD_append _ _ _ _ before
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  let agree (lo hi old new : List Bool) := ∀ i,
    (lo.getD i false = true → hi.getD i false = true) ∧
      old.getD i false = (lo.getD i false || (hi.getD i false && new.getD i false))
  have evalAnd (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    cases a <;> cases b <;> rfl
  have evalOr (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    cases a <;> cases b <;> rfl
  have evalUnary (op : GateOp) (hop : op = .and ∨ op = .or) (v : Bool) : op.eval [v] = v := by
    rcases hop with rfl | rfl <;> cases v <;> rfl
  have evalCopy (ws : List Bool) (w : ℕ) : evalGate ws (copy w) = ws.getD w false := by
    change GateOp.or.eval [ws.getD w false, ws.getD w false] = _
    rw [evalOr, Bool.or_self]
  have sameGate (lo hi old new : List Bool) (g : Gate) (hop : g.op = .and ∨ g.op = .or)
      (hg : g.inputs.length ≤ 2) (h : agree lo hi old new) :
      (evalGate lo g = true → evalGate hi g = true) ∧
        evalGate old g = (evalGate lo g || (evalGate hi g && evalGate new (patch lo hi g))) := by
    rcases g with ⟨op, inputs⟩
    change op = .and ∨ op = .or at hop
    change inputs.length ≤ 2 at hg
    cases inputs with
    | nil =>
      rcases hop with rfl | rfl <;> exact ⟨id, rfl⟩
    | cons a rest =>
      cases rest with
      | nil =>
        obtain ⟨ok, ha⟩ := h a
        cases la : lo.getD a false <;> cases ha' : hi.getD a false <;>
          simp only [la, ha', Bool.false_eq_true, false_implies, true_implies] at ok <;>
          simp only [evalGate, patch, List.map_cons, List.map_nil, List.getD_cons_zero,
            List.getD_cons_succ, List.getD_nil, live, la, ha', ha,
            Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_false,
            Bool.and_true, Bool.false_or, Bool.true_or, Bool.false_eq_true,
            ↓reduceIte, evalUnary op hop, copy, evalOr, Bool.or_self,
            List.getD_eq_default hi false le_rfl, false_implies, and_self, imp_self]
      | cons b rest =>
        cases rest with
        | nil =>
          obtain ⟨oka, ha⟩ := h a
          obtain ⟨okb, hb⟩ := h b
          rcases hop with rfl | rfl <;>
            cases al : lo.getD a false <;> cases ah : hi.getD a false <;>
            cases bl : lo.getD b false <;> cases bh : hi.getD b false <;>
            simp only [al, ah, bl, bh, Bool.false_eq_true, false_implies, true_implies] at oka okb <;>
            simp only [evalGate, patch, List.map_cons, List.map_nil, List.getD_cons_zero,
              List.getD_cons_succ, copy, evalAnd, evalOr, live, ha, hb, al, ah, bl, bh,
              Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_false,
              Bool.and_true, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
              Bool.false_eq_true, ↓reduceIte, Bool.or_self, false_implies, and_self, imp_self]
        | cons c rest => simp only [List.length_cons] at hg; omega
  have agreeStep (lo hi old new : List Bool) (g : Gate) (hop : g.op = .and ∨ g.op = .or)
      (hg : g.inputs.length ≤ 2) (hl : lo.length = hi.length) (ho : old.length = hi.length)
      (hn : new.length = hi.length) (h : agree lo hi old new) :
      agree (advance lo g) (advance hi g) (advance old g) (advance new (patch lo hi g)) := by
    intro i
    change ((lo ++ [_]).getD i false = true → (hi ++ [_]).getD i false = true) ∧
      (old ++ [_]).getD i false = ((lo ++ [_]).getD i false ||
        ((hi ++ [_]).getD i false && (new ++ [_]).getD i false))
    simp only [readAppend, hl, ho, hn]
    by_cases hi' : i = hi.length
    · simpa only [ite_eq_left hi'] using sameGate lo hi old new g hop hg h
    · simpa only [ite_eq_right hi'] using h i
  have agreeBuild (gs : List Gate) (lo hi old new : List Bool) (hv : simple gs)
      (hl : lo.length = hi.length) (ho : old.length = hi.length) (hn : new.length = hi.length)
      (h : agree lo hi old new) :
      agree (gs.foldl advance lo) (gs.foldl advance hi) (gs.foldl advance old)
        ((build lo hi gs).foldl advance new) := by
    induction gs generalizing lo hi old new with
    | nil => exact h
    | cons g gs ih =>
      rw [buildCons]
      simp only [List.foldl_cons]
      apply ih
      · exact fun g' hm => hv g' (List.mem_cons_of_mem _ hm)
      · simp only [advanceLen, hl]
      · simp only [advanceLen, ho]
      · simp only [advanceLen, hn]
      · exact agreeStep lo hi old new g (hv g (by simp)).1 (hv g (by simp)).2 hl ho hn h
  have original : simple C.gates := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hC g hg
  let lo := List.ofFn (fun _ : Fin 25 => false)
  let hi := List.ofFn (fun _ : Fin 25 => true)
  let D : Circuit := ⟨build lo hi C.gates, C.output⟩
  have dSize : D.size = C.size := buildLen _ _ _
  have dValid : valid 25 D.gates := buildValid C.gates lo hi (by simp [hi]) original
  have gateEq (gs : List Gate) (j : ℕ) (g : Gate) (h : gs[j]? = some g) :
      gs.getD j ⟨.or, []⟩ = g := by
    simp only [List.getD_eq_getElem?_getD, h, Option.getD_some]
  have dModel : IsAO2 25 D := by
    have atPos (j : ℕ) (hj : j < D.gates.length) : legal (25 + j) (gateAt D j) := by
      have hg := List.getElem?_eq_getElem hj
      have h := dValid j D.gates[j] hg
      change legal (25 + j) (D.gates.getD j ⟨.or, []⟩)
      rwa [gateEq _ _ _ hg]
    have onMember (g : Gate) (hg : g ∈ D.gates) : ∃ n, legal n g := by
      obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hg
      refine ⟨25+i, ?_⟩
      have h := atPos i hi
      change legal (25 + i) (D.gates.getD i ⟨.or, []⟩) at h
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
  have low : C.eval lo = false := by
    cases h : C.eval lo
    · rfl
    · obtain ⟨p, l, _, hf, _⟩ := (hCorrect (fun _ => false)).mp h
      cases hf
  have high : C.eval hi = true := by
    obtain ⟨p, l, h⟩ := someEdge
    exact (hCorrect (fun _ => true)).mpr ⟨p, l, h, rfl, rfl⟩
  have dEval (x : Fin 25 → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    have initial : agree lo hi (List.ofFn x) (List.ofFn x) := by
      intro w
      by_cases h : w < 25
      · simp only [lo, hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left h,
          Option.getD_some, Bool.true_and, Bool.false_or, Bool.false_eq_true, false_implies, true_and]
      · simp only [lo, hi, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right h,
          Option.getD_none, Bool.false_and, Bool.false_or, Bool.false_eq_true, false_implies, true_and]
    have h := agreeBuild C.gates lo hi (List.ofFn x) (List.ofFn x) original
      (by simp [lo, hi]) (by simp [hi]) (by simp [hi]) initial C.output |>.2
    change C.eval (List.ofFn x) = (C.eval lo || C.eval hi && D.eval (List.ofFn x)) at h
    simpa only [low, high, Bool.true_and, Bool.false_or] using h.symm
  rw [← dSize]
  apply exactBinary D dModel
  intro x
  rw [dEval]
  exact hCorrect x
