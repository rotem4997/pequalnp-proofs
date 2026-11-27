import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 1400000 in
theorem PEqualNP.Outside.R_meta_1667_2
    (hand : ∀ (m : Fin 14) (code : Fin m.val → Fin 3 × Fin 24 × Fin 24),
      (∀ j : Fin m.val, let g := code j
        g.2.1 ≤ g.2.2 ∧ (g.1 = 2 → g.2.1 = g.2.2) ∧
        (g.2.1.val < 10 + j.val ∨ g.2.1 = 23) ∧ (g.2.2.val < 10 + j.val ∨ g.2.2 = 23)) →
      ∀ a b : Fin 24, a ≤ b →
        (a.val < 10 + m.val ∨ a = 23) → (b.val < 10 + m.val ∨ b = 23) → ∃ x : Fin 9 → Bool,
        let w := (List.ofFn code).foldl (fun (v : List Bool) g =>
          let u := v.getD g.2.1.val false
          let z := v.getD g.2.2.val false
          v ++ [if g.1 = 0 then u && z else if g.1 = 1 then u || z else !u])
          (List.ofFn x ++ [x 0 && x 1])
        (w.getD a.val false && w.getD b.val false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (hor : ∀ (m : Fin 14) (code : Fin m.val → Fin 3 × Fin 24 × Fin 24),
      (∀ j : Fin m.val, let g := code j
        g.2.1 ≤ g.2.2 ∧ (g.1 = 2 → g.2.1 = g.2.2) ∧
        (g.2.1.val < 10 + j.val ∨ g.2.1 = 23) ∧ (g.2.2.val < 10 + j.val ∨ g.2.2 = 23)) →
      ∀ a b : Fin 24, a ≤ b →
        (a.val < 10 + m.val ∨ a = 23) → (b.val < 10 + m.val ∨ b = 23) → ∃ x : Fin 9 → Bool,
        let w := (List.ofFn code).foldl (fun (v : List Bool) g =>
          let u := v.getD g.2.1.val false
          let z := v.getD g.2.2.val false
          v ++ [if g.1 = 0 then u && z else if g.1 = 1 then u || z else !u])
          (List.ofFn x ++ [x 0 && x 1])
        (w.getD a.val false || w.getD b.val false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (hnot : ∀ (m : Fin 14) (code : Fin m.val → Fin 3 × Fin 24 × Fin 24),
      (∀ j : Fin m.val, let g := code j
        g.2.1 ≤ g.2.2 ∧ (g.1 = 2 → g.2.1 = g.2.2) ∧
        (g.2.1.val < 10 + j.val ∨ g.2.1 = 23) ∧ (g.2.2.val < 10 + j.val ∨ g.2.2 = 23)) →
      ∀ a : Fin 24, (a.val < 10 + m.val ∨ a = 23) → ∃ x : Fin 9 → Bool,
        let w := (List.ofFn code).foldl (fun (v : List Bool) g =>
          let u := v.getD g.2.1.val false
          let z := v.getD g.2.2.val false
          v ++ [if g.1 = 0 then u && z else if g.1 = 1 then u || z else !u])
          (List.ofFn x ++ [x 0 && x 1])
        (!(w.getD a.val false)) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let target (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let initial (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 1]
  let opVal (k : Fin 3) (u v : Bool) :=
    if k = 0 then u && v else if k = 1 then u || v else !u
  let value (w : List Bool) (g : Fin 3 × Fin 24 × Fin 24) :=
    opVal g.1 (w.getD g.2.1.val false) (w.getD g.2.2.val false)
  let encodedStep (w : List Bool) (g : Fin 3 × Fin 24 × Fin 24) := w ++ [value w g]
  let gateStep (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let legal (n : ℕ) (g : Fin 3 × Fin 24 × Fin 24) :=
    g.2.1 ≤ g.2.2 ∧ (g.1 = 2 → g.2.1 = g.2.2) ∧
      (g.2.1.val < n ∨ g.2.1 = 23) ∧ (g.2.2.val < n ∨ g.2.2 = 23)
  let pin (n i : ℕ) : Fin 24 :=
    if h : i < min n 23 then ⟨i, by omega⟩ else 23
  let pack (n : ℕ) (k : Fin 3) (i j : ℕ) : Fin 3 × Fin 24 × Fin 24 :=
    let a := pin n i
    let b := pin n j
    if k = 2 then (k, a, a) else if a ≤ b then (k, a, b) else (k, b, a)
  have pin_ok (n i : ℕ) : (pin n i).val < n ∨ pin n i = 23 := by
    dsimp only [pin]
    split
    · left
      change i < n
      omega
    · exact Or.inr rfl
  have pin_read (w : List Bool) (n i : ℕ) (hw : w.length = n) (hn : n ≤ 23) :
      w.getD (pin n i).val false = w.getD i false := by
    dsimp only [pin]
    split
    · rfl
    · rename_i hi
      have h₁ : w.length ≤ i := by omega
      have h₂ : w.length ≤ 23 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h₁, List.getElem?_eq_none h₂]
  have pack_ok (n : ℕ) (k : Fin 3) (i j : ℕ) : legal n (pack n k i j) := by
    by_cases hk : k = 2
    · simpa [legal, pack, hk] using pin_ok n i
    · by_cases hab : pin n i ≤ pin n j
      · simp [legal, pack, hk, hab, pin_ok]
      · have hba : pin n j ≤ pin n i := le_of_not_ge hab
        simp [legal, pack, hk, hab, hba, pin_ok]
  have pack_value (w : List Bool) (n : ℕ) (k : Fin 3) (i j : ℕ)
      (hw : w.length = n) (hn : n ≤ 23) :
      value w (pack n k i j) = opVal k (w.getD i false) (w.getD j false) := by
    have ra := pin_read w n i hw hn
    have rb := pin_read w n j hw hn
    by_cases hk : k = 2
    · subst k
      simp only [pack, ite_eq_left rfl, value, ra]
      rfl
    · by_cases hab : pin n i ≤ pin n j
      · simp only [pack, ite_eq_right hk, ite_eq_left hab, value, ra, rb]
      · have comm (a b : Bool) : opVal k b a = opVal k a b := by
          by_cases h0 : k = 0
          · simpa only [opVal, ite_eq_left h0] using Bool.and_comm b a
          · have h1 : k = 1 := by omega
            simpa only [opVal, ite_eq_right h0, ite_eq_left h1] using Bool.or_comm b a
        simpa only [pack, ite_eq_right hk, ite_eq_right hab, value, ra, rb] using
          comm (w.getD i false) (w.getD j false)
  let shape (op : GateOp) (pins : List ℕ) : Fin 3 × ℕ × ℕ :=
    let a := pins.headD 23
    let b := pins.tail.headD a
    GateOp.rec (motive := fun _ => Fin 3 × ℕ × ℕ)
      (if pins.isEmpty then (2, 23, 23) else (0, a, b)) (1, a, b)
      (2, a, a) (fun _ => (1, a, b)) (1, a, b) op
  let admissible (g : Gate) :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  have shape_value (w : List Bool) (hw : w.length ≤ 23) (g : Gate) (hg : admissible g) :
      let s := shape g.op g.inputs
      opVal s.1 (w.getD s.2.1 false) (w.getD s.2.2 false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    have zero : w[23]?.getD false = false := by
      simp [List.getElem?_eq_none hw]
    obtain ⟨op, pins⟩ := g
    obtain ⟨hop, hlen⟩ := hg
    change op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) at hop
    change pins.length ≤ 2 at hlen
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have forms : pins = [] ∨ (∃ a, pins = [a]) ∨ ∃ a b, pins = [a, b] := by
      cases pins with
      | nil => simp
      | cons a rest =>
        cases rest with
        | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
        | cons b rest =>
          have he : rest.length = 0 := by simpa using hlen
          simp only [List.length_eq_zero_iff] at he
          exact Or.inr (Or.inr ⟨a, b, by rw [he]⟩)
    rcases hop with rfl | rfl | rfl
    · change _ = (pins.map fun i => w.getD i false).all id
      rcases forms with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;> simp [shape, opVal, zero]
    · change _ = (pins.map fun i => w.getD i false).any id
      rcases forms with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;> simp [shape, opVal, zero]
    · change _ = !((pins.map fun i => w.getD i false).headD false)
      rcases forms with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;> simp [shape, opVal, zero]
  have compile (gs : List Gate) (n : ℕ) (bound : n + gs.length ≤ 23)
      (ok : ∀ g ∈ gs, admissible g) :
      ∃ p : List (Fin 3 × Fin 24 × Fin 24), p.length = gs.length ∧
        (∀ e ∈ p.zipIdx n, legal e.2 e.1) ∧
        ∀ w : List Bool, w.length = n → p.foldl encodedStep w = gs.foldl gateStep w := by
    induction gs generalizing n with
    | nil => exact ⟨[], rfl, by simp, by simp⟩
    | cons g gs ih =>
      let s := shape g.op g.inputs
      let a := pack n s.1 s.2.1 s.2.2
      simp only [List.length_cons] at bound
      obtain ⟨p, hp, hl, he⟩ := ih (n + 1) (by omega)
        (fun t ht => ok t (List.mem_cons_of_mem g ht))
      refine ⟨a :: p, by simp [hp], ?_, ?_⟩
      · intro e h
        rw [List.zipIdx_cons, List.mem_cons] at h
        rcases h with rfl | h
        · exact pack_ok n s.1 s.2.1 s.2.2
        · exact hl e h
      · intro w hw
        have hval := (pack_value w n s.1 s.2.1 s.2.2 hw (by omega)).trans
          (shape_value w (by omega) g (ok g (by simp)))
        have hstep : encodedStep w a = gateStep w g := congrArg (fun b => w ++ [b]) hval
        simp only [List.foldl_cons, hstep]
        apply he
        simp [gateStep, hw]
  have impossible (p : List (Fin 3 × Fin 24 × Fin 24)) (hp : p.length ≤ 13)
      (hl : ∀ e ∈ p.zipIdx 10, legal e.2 e.1)
      (c : Fin 3 × Fin 24 × Fin 24) (hc : legal (10 + p.length) c)
      (works : ∀ x, value (p.foldl encodedStep (initial x)) c = target x) : False := by
    let m : Fin 14 := ⟨p.length, by omega⟩
    let code : Fin m.val → Fin 3 × Fin 24 × Fin 24 := p.get
    have back : List.ofFn code = p := List.ofFn_get p
    have good (j : Fin m.val) : legal (10 + j.val) (code j) := by
      apply hl (code j, 10 + j.val)
      rw [List.mem_zipIdx_iff_le_and_getElem?_sub]
      change 10 ≤ 10 + j.val ∧ p[10 + j.val - 10]? = some (p.get j)
      constructor
      · omega
      · rw [show 10 + j.val - 10 = j.val by omega, List.getElem?_eq_getElem j.isLt]
        rfl
    obtain ⟨k, a, b⟩ := c
    fin_cases k
    · obtain ⟨x, hx⟩ := hand m code good a b hc.1 hc.2.2.1 hc.2.2.2
      rw [back] at hx
      exact hx (works x)
    · obtain ⟨x, hx⟩ := hor m code good a b hc.1 hc.2.2.1 hc.2.2.2
      rw [back] at hx
      exact hx (works x)
    · obtain ⟨x, hx⟩ := hnot m code good a hc.2.2.1
      rw [back] at hx
      exact hx (works x)
  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl gateStep w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, gateStep, List.length_append,
        List.length_cons, List.length_nil]; omega
  have init_length (x : Fin 9 → Bool) : (initial x).length = 10 := by simp [initial]
  have exclude (pre : List Gate) (hp : pre.length ≤ 13) (ok : ∀ g ∈ pre, admissible g)
      (k : Fin 3) (i j : ℕ)
      (found : ∀ x, let w := pre.foldl gateStep (initial x)
        opVal k (w.getD i false) (w.getD j false) = target x) : False := by
    obtain ⟨p, hlen, hl, he⟩ := compile pre 10 (by omega) ok
    let n := 10 + pre.length
    apply impossible p (by omega) hl (pack n k i j) (by rw [hlen]; exact pack_ok n k i j)
    intro x
    rw [he (initial x) (init_length x)]
    have hw : (pre.foldl gateStep (initial x)).length = n := by
      rw [fold_length, init_length]
    exact (pack_value _ n k i j hw (by dsimp [n]; omega)).trans (found x)
  have append_read (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases hi : i < w.length
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ite_eq_right (Nat.ne_of_lt hi)]
    · by_cases he : i = w.length
      · subst i
        simp [List.getD_eq_getElem?_getD]
      · have hw : (w ++ [b]).length ≤ i := by simp only [List.length_append,
            List.length_cons, List.length_nil]; omega
        have hw' : w.length ≤ i := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw,
          List.getElem?_eq_none hw', ite_eq_right he]
  have preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl gateStep w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (gateStep w g) (by simp [gateStep]; omega)]
      exact (append_read w _ i).trans (ite_eq_right (Nat.ne_of_lt hi))
  intro C hfan hhead hfun
  by_contra hshort
  obtain ⟨gates, out⟩ := C
  cases gates with
  | nil =>
    have h := hhead (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    simp [List.getD_eq_getElem?_getD] at h
  | cons first tail =>
    have small : tail.length ≤ 14 := by
      change ¬16 ≤ (first :: tail).length at hshort
      simp only [List.length_cons] at hshort
      omega
    have ok (g : Gate) (hg : g ∈ tail) : admissible g :=
      hfan g (List.mem_cons_of_mem first hg)
    have agree (x : Fin 9 → Bool) :
        (tail.foldl gateStep (initial x)).getD out false = target x := by
      have h := hhead x
      change (tail.foldl gateStep (gateStep (List.ofFn x) first)).getD 9 false = _ at h
      rw [preserved tail _ 9 (by simp [gateStep])] at h
      change (List.ofFn x ++ [_]).getD 9 false = _ at h
      rw [append_read, ite_eq_left (by simp)] at h
      have step : gateStep (List.ofFn x) first = initial x := congrArg (fun b => List.ofFn x ++ [b]) h
      have hf := congrFun hfun x
      change (tail.foldl gateStep (gateStep (List.ofFn x) first)).getD out false = target x at hf
      rwa [step] at hf
    rcases List.eq_nil_or_concat tail with ht | ⟨pre, last, ht⟩
    · subst tail
      apply exclude [] (by simp) (by simp) 1 out out
      intro x
      simpa [opVal] using agree x
    · have hx : tail = pre ++ [last] := by simpa using ht
      clear ht
      subst tail
      have hp : pre.length ≤ 13 := by
        simp only [List.length_append, List.length_cons, List.length_nil] at small
        omega
      have preOK : ∀ g ∈ pre, admissible g := fun g hg => ok g (by simp [hg])
      have lastOK : admissible last := ok last (by simp)
      let n := 10 + pre.length
      have size (x : Fin 9 → Bool) : (pre.foldl gateStep (initial x)).length = n := by
        rw [fold_length, init_length]
      have final (x : Fin 9 → Bool) :
          (gateStep (pre.foldl gateStep (initial x)) last).getD out false = target x := by
        simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using agree x
      by_cases hlast : out = n
      · let s := shape last.op last.inputs
        apply exclude pre hp preOK s.1 s.2.1 s.2.2
        intro x
        let w := pre.foldl gateStep (initial x)
        have hw : w.length = n := size x
        have h := final x
        change (w ++ [_]).getD out false = _ at h
        rw [append_read, ite_eq_left (hlast.trans hw.symm)] at h
        exact (shape_value w (by dsimp [n] at hw; omega) last lastOK).trans h
      · apply exclude pre hp preOK 1 out out
        intro x
        let w := pre.foldl gateStep (initial x)
        have hw : w.length = n := size x
        have h := final x
        change (w ++ [_]).getD out false = _ at h
        rw [append_read, ite_eq_right (fun eq => hlast (eq.trans hw))] at h
        simpa [opVal, w] using h
