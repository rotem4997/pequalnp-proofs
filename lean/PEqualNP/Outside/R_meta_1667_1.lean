import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1667_1
    (h1 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 1]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h2 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 1]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h3 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 1]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let target : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let init (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 1]
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (step w g) hlt]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have headVal (g : PEqualNP.CircuitLowerBounds.Gate) (tail : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g :: tail, o⟩ (List.ofFn x)).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
    let w := List.ofFn x
    have hl : w.length = 9 := by simp [w]
    change (tail.foldl step (step w g)).getD 9 false = _
    rw [preserved tail (step w g) 9 (by simp [step, hl])]
    simpa only [step, w, List.length_ofFn] using
      atEnd (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))
  have pad (w : List Bool) (o : ℕ) : (w ++ [false]).getD o false = w.getD o false := by
    by_cases h : o < w.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · have h' : w.length ≤ o := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h',
        List.getElem?_eq_none h', Option.getD_none]
      cases o - w.length <;> rfl
  intro C hfan hhead hfun
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil =>
    have bad := hhead (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at bad
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp :
      (List.ofFn (fun _ : Fin 9 => true)).length ≤ 9)] at bad
    cases bad
  | cons g tail =>
    have agree (x : Fin 9 → Bool) :
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨tail, o⟩ (init x) = target x := by
      have hg := (headVal g tail o x).symm.trans (hhead x)
      have hh := congrFun hfun x
      change (tail.foldl step (List.ofFn x ++ [g.op.eval
        (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false = target x at hh
      rw [hg] at hh
      exact hh
    cases tail with
    | nil =>
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], o⟩
      have hf : PEqualNP.MetaComplexity.FanInTwo D := by
        intro a ha
        change a ∈ ([] : List PEqualNP.CircuitLowerBounds.Gate) at ha
        cases ha
      obtain ⟨x, hx⟩ := h2 [] (by decide) D hf (by change 0 ≤ 13; decide)
      change (init x ++ [false]).getD o false ≠ target x at hx
      exact False.elim (hx ((pad (init x) o).trans (agree x)))
    | cons k rest =>
      by_contra short
      change ¬ 16 ≤ (g :: k :: rest).length at short
      simp only [List.length_cons] at short
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨rest, o⟩
      have hd : PEqualNP.MetaComplexity.FanInTwo D := by
        intro a ha
        exact hfan a (List.mem_cons_of_mem g (List.mem_cons_of_mem k ha))
      have hs : D.size ≤ 13 := by
        change rest.length ≤ 13
        omega
      have hk := hfan k (List.mem_cons_of_mem g (List.mem_cons_self ..))
      obtain ⟨hop, hlen⟩ := hk
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      have bad : ∃ x : Fin 9 → Bool, D.eval (step (init x) k) ≠ target x := by
        rcases hop with h | h | h
        · simpa only [step, h] using h1 k.inputs hlen D hd hs
        · simpa only [step, h] using h2 k.inputs hlen D hd hs
        · simpa only [step, h] using h3 k.inputs hlen D hd hs
      obtain ⟨x, hx⟩ := bad
      exact hx (agree x)
