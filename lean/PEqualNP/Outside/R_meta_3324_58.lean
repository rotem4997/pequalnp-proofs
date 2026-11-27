import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Each column is one input wire on 21 edge rows followed by 37 maximal independent sets.
-- A gate evaluates all 58 rows with one bitwise operation.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3324_58
    (synthesize :
      let columns : List ℕ :=
        [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240,
         14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250,
         218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728,
         288160007407550752]
      let step := fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [if g.op.eval [true, false] then a ||| b else a &&& b]
      ∃ C : Circuit, IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        2 ≤ C.size ∧ C.size ≤ 26 ∧ (C.gates.foldl step columns).getD C.output 0 = 2097151)
    (simulate : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (initial : List ℕ) (r : ℕ),
    let step := fun (w : List ℕ) (g : Gate) =>
      let a := w.getD (g.inputs.getD 0 0) 0
      let b := w.getD (g.inputs.getD 1 0) 0
      w ++ [if g.op.eval [true, false] then a ||| b else a &&& b]
    ((C.gates.foldl step initial).getD C.output 0).testBit r =
      C.eval (initial.map fun a => a.testBit r)) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ (2 : ℕ) ≤ x2.size ∧ x2.size ≤ (26 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Decidable.decide (∃ (x4 : Fin (14 : ℕ)) (x5 : Fin (14 : ℕ)), (↑x4, ↑x5) ∈ x1 ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) := by
  let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let cols : List ℕ :=
    [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240,
     14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608,
     183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  -- Each seven-bit point subset indexes a negative row covering every compatible line.
  let slot : List ℕ :=
    [57, 56, 45, 44, 37, 35, 36, 32, 51, 49, 30, 21, 31, 25, 28, 21, 42, 41, 40, 38, 26, 25, 21, 21, 27,
     25, 23, 21, 25, 25, 21, 21, 53, 52, 34, 32, 33, 32, 32, 32, 48, 46, 23, 21, 21, 21, 21, 21, 24, 21,
     23, 21, 22, 21, 21, 21, 23, 21, 23, 21, 21, 21, 21, 21, 55, 54, 43, 38, 29, 21, 28, 21, 50, 46, 28,
     21, 28, 21, 28, 21, 39, 38, 38, 38, 22, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 47, 46, 21, 21,
     22, 21, 21, 21, 46, 46, 21, 21, 21, 21, 21, 21, 22, 21, 21, 21, 22, 21, 21, 21, 21, 21, 21, 21, 21,
     21, 21, 21]
  let row (r : ℕ) (i : Fin 14) := (cols.getD i.val 0).testBit r
  let step (w : List ℕ) (g : Gate) :=
    let a := w.getD (g.inputs.getD 0 0) 0
    let b := w.getD (g.inputs.getD 1 0) 0
    w ++ [if g.op.eval [true, false] then a ||| b else a &&& b]
  obtain ⟨C, hao, hnd, hlo, hhi, hw⟩ := synthesize
  change (C.gates.foldl step cols).getD C.output 0 = 2097151 at hw
  have rows (r : ℕ) : C.eval (List.ofFn (row r)) = (2097151 : ℕ).testBit r := by
    have hp := simulate 14 C hao cols r
    change ((C.gates.foldl step cols).getD C.output 0).testBit r = _ at hp
    rw [hw] at hp
    have he : List.ofFn (row r) = cols.map (fun a => a.testBit r) := by
      apply List.ext_getElem
      · simp [cols]
      · intro k hk hk'
        have h : k < cols.length := by simpa using hk'
        rw [List.getElem_ofFn, List.getElem_map]
        simp only [row, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    rw [he, ← hp]
  let stepB (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have liftWires (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (l u : List Bool) (len : l.length = u.length)
      (rise : ∀ i, l.getD i false = true → u.getD i false = true) :
      ∀ i, (gs.foldl stepB l).getD i false = true → (gs.foldl stepB u).getD i false = true := by
    induction gs generalizing l u with
    | nil => exact rise
    | cons g gs ih =>
      apply ih (fun a ha => ops a (List.mem_cons_of_mem _ ha)) _ _ (by simp [stepB, len])
      have gateRise : g.op.eval (g.inputs.map fun j => l.getD j false) = true →
          g.op.eval (g.inputs.map fun j => u.getD j false) = true := by
        rcases ops g (by simp) with h | h
        · rw [h]
          change (g.inputs.map _).all id = true → (g.inputs.map _).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id]
          exact fun hl j hj => rise j (hl j hj)
        · rw [h]
          change (g.inputs.map _).any id = true → (g.inputs.map _).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id]
          rintro ⟨j, hj, ht⟩
          exact ⟨j, hj, rise j ht⟩
      intro i
      dsimp only [stepB]
      by_cases h : i < l.length
      · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (len ▸ h)]
        exact rise i
      · have hu : u.length ≤ i := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ hu, len]
        cases i - u.length with
        | zero => exact gateRise
        | succ j => simp [List.getD_eq_getElem?_getD]
  have input {k : ℕ} (f : Fin k → Bool) (i : Fin k) :
      (List.ofFn f).getD i.val false = f i := by simp
  have mono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply liftWires C.gates hao.1 _ _ (by simp) _ C.output
    intro i
    by_cases hi : i < 14
    · rw [input x ⟨i,hi⟩, input y ⟨i,hi⟩]
      exact h ⟨i,hi⟩
    · simp [List.getD_eq_getElem?_getD, hi]
  -- These finite certificates cover every true input from below and every false input from above.
  have low : ∀ i j : Fin 14, (i.val, j.val) ∈ E →
      ∃ r : Fin 21, ∀ k : Fin 14, row r.val k = true → k = i ∨ k = j := by decide
  have ones : ∀ r : Fin 21, (2097151 : ℕ).testBit r.val = true := by decide
  have zeros : ∀ a : Fin 128, (2097151 : ℕ).testBit (slot.getD a.val 0) = false := by decide
  have cover : ∀ (a : Fin 128) (j : Fin 14),
      ((j.val < 7 ∧ a.val.testBit j.val = true) ∨
       (7 ≤ j.val ∧ ∀ i : Fin 7, a.val.testBit i.val = true → (i.val, j.val) ∉ E)) →
      row (slot.getD a.val 0) j = true := by decide
  refine ⟨C, hao, hnd, hlo, hhi, ?_⟩
  intro x
  change C.eval (List.ofFn x) = decide (∃ i j : Fin 14, (i.val, j.val) ∈ E ∧ x i = true ∧ x j = true)
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro hx
    by_contra noedge
    let bs := List.ofFn (fun i : Fin 7 => x ⟨i.val, by omega⟩)
    let bv := BitVec.ofBoolListLE bs
    have bound : bv.toNat < 128 := by
      have h := bv.isLt
      simpa [bv, bs] using h
    let a : Fin 128 := ⟨bv.toNat, bound⟩
    have bits (i : Fin 7) : a.val.testBit i.val = x ⟨i.val, by omega⟩ := by
      change bv.toNat.testBit i.val = _
      rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
      exact input (fun j : Fin 7 => x ⟨j.val, by omega⟩) i
    have upper (j : Fin 14) (hj : x j = true) : row (slot.getD a.val 0) j = true := by
      apply cover
      by_cases h : j.val < 7
      · exact Or.inl ⟨h, (bits ⟨j.val,h⟩).trans hj⟩
      · refine Or.inr ⟨by omega, ?_⟩
        intro i hi edge
        exact noedge ⟨⟨i.val, by omega⟩, j, edge, (bits i).symm.trans hi, hj⟩
    have bad := mono x _ upper hx
    rw [rows, zeros a] at bad
    contradiction
  · rintro ⟨i, j, edge, hi, hj⟩
    obtain ⟨r, hr⟩ := low i j edge
    apply mono (row r.val) x
    · intro k hk
      rcases hr k hk with rfl | rfl
      · exact hi
      · exact hj
    · exact (rows r.val).trans (ones r)
