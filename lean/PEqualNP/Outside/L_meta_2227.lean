import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2227_aux

private def scan (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

private theorem scan_cons (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

private theorem scan_append (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

private theorem scan_length (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [scan_cons, ih]; simp; omega

private theorem scan_prefix (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem read_gate (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
    (ha : a < w.length + j) (hb : b < w.length + j) (op : α → α → α)
    (hstep : ∀ p, step p gs[j] = op (p.getD a d) (p.getD b d)) :
    (scan step gs w).getD (w.length + j) d =
      op ((scan step gs w).getD a d) ((scan step gs w).getD b d) := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j+1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre (i : ℕ) (hi : i < w.length + j) : (scan step gs w).getD i d = pre.getD i d := by
    rw [hs]
    exact scan_prefix _ _ _ _ _ (by omega)
  rw [hpre a ha, hpre b hb, hs, scan_cons, scan_prefix _ _ _ _ _ (by simp [hp]),
    List.getD_append_right _ _ _ _ (by omega)]
  simpa [hp] using hstep pre

private def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private theorem inputValue (C : Circuit) (x : Fin 14 → Bool) (i : Fin 14) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (scan gateValue C.gates (List.ofFn x)).getD i.val false = _
  rw [scan_prefix _ _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem valueAt (C : Circuit) (x : Fin 14 → Bool) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (ha : a < 14 + j) (hb : b < 14 + j)
    (op : Bool → Bool → Bool)
    (h : ∀ w, gateValue w C.gates[j] = op (w.getD a false) (w.getD b false)) :
    (C.wires (List.ofFn x)).getD (14+j) false =
      op ((C.wires (List.ofFn x)).getD a false) ((C.wires (List.ofFn x)).getD b false) := by
  change (scan gateValue C.gates (List.ofFn x)).getD (14+j) false =
    op ((scan gateValue C.gates (List.ofFn x)).getD a false)
      ((scan gateValue C.gates (List.ofFn x)).getD b false)
  simpa only [List.length_ofFn] using
    read_gate gateValue C.gates (List.ofFn x) false j hj a b
      (by simpa only [List.length_ofFn] using ha) (by simpa only [List.length_ofFn] using hb) op h

private def inputDegrees (p : Fin 14) : List ℕ :=
  (List.range 14).map fun i => if i ∈ ({p.val} : Finset ℕ) then 1 else 0

private theorem inputDegree (C : Circuit) (p : Fin 14) (i : ℕ) (hi : i < 14) :
    (C.lineDegrees 14 {p.val}).getD i 0 = if i = p.val then 1 else 0 := by
  change (scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD i 0 = _
  rw [scan_prefix _ _ _ _ _ (by simpa [inputDegrees] using hi),
    List.getD_eq_getElem _ _ (by simpa [inputDegrees] using hi)]
  simp [inputDegrees]

private theorem degreeAt (C : Circuit) (p : Fin 14) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (ha : a < 14 + j) (hb : b < 14 + j) (op : ℕ → ℕ → ℕ)
    (h : ∀ w, C.gates[j].lineDegree w = op (w.getD a 0) (w.getD b 0)) :
    (C.lineDegrees 14 {p.val}).getD (14+j) 0 =
      op ((C.lineDegrees 14 {p.val}).getD a 0) ((C.lineDegrees 14 {p.val}).getD b 0) := by
  change (scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD (14+j) 0 =
    op ((scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD a 0)
      ((scan (fun w g => g.lineDegree w) C.gates (inputDegrees p)).getD b 0)
  have hlen : (inputDegrees p).length = 14 := by simp [inputDegrees]
  simpa only [hlen] using
    read_gate (fun w g => g.lineDegree w) C.gates (inputDegrees p) 0 j hj a b
      (by simpa [hlen] using ha) (by simpa [hlen] using hb) op h

private def invariant (degree : ℕ) (old updated derivative : Bool) : Prop :=
  (degree = 0 → updated = old) ∧
  (degree ≤ 1 → updated = true → old = true ∨ derivative = true)

private theorem and_step (a b : ℕ) (u u' du v v' dv : Bool)
    (hu : invariant a u u' du) (hv : invariant b v v' dv) :
    invariant (a+b) (u && v) (u' && v') (u && dv || du && v) := by
  constructor
  · intro h
    rw [hu.1 (by omega), hv.1 (by omega)]
  · intro hd h
    obtain ⟨hu', hv'⟩ : u' = true ∧ v' = true := by simpa only [Bool.and_eq_true] using h
    by_cases ha : a = 0
    · have he : u = true := (hu.1 ha).symm.trans hu'
      rcases hv.2 (by omega) hv' with hn | hd'
      · exact Or.inl (by simp [he, hn])
      · exact Or.inr (by simp [he, hd'])
    · have he : v = true := (hv.1 (by omega)).symm.trans hv'
      rcases hu.2 (by omega) hu' with hn | hd'
      · exact Or.inl (by simp [he, hn])
      · exact Or.inr (by simp [he, hd'])

private theorem or_step (a b : ℕ) (u u' du v v' dv : Bool)
    (hu : invariant a u u' du) (hv : invariant b v v' dv) :
    invariant (max a b) (u || v) (u' || v') (du || dv) := by
  have h1 := le_max_left a b
  have h2 := le_max_right a b
  constructor
  · intro h
    rw [hu.1 (by omega), hv.1 (by omega)]
  · intro hd h
    have ht : u' = true ∨ v' = true := by simpa only [Bool.or_eq_true] using h
    rcases ht with h | h
    · rcases hu.2 (by omega) h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    · rcases hv.2 (by omega) h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])

private theorem result (C : Circuit) (p : Fin 14) (x : Fin 14 → Bool) (d : ℕ → Bool)
    (hg : ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j)
    (hd : ∀ i : Fin 14, d i.val = decide (p = i))
    (hgate : ∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = .and → d (14+j) =
        ((C.wires (List.ofFn x)).getD a false && d b ||
          d a && (C.wires (List.ofFn x)).getD b false)) ∧
      (g.op = .or → d (14+j) = (d a || d b)))
    (hfalse : C.eval (List.ofFn x) = false)
    (htrue : C.eval (List.ofFn (fun i => if p = i then true else x i)) = true)
    (hzero : d C.output = false) :
    2 ≤ C.lineDeg 14 {p.val} := by
  let y : Fin 14 → Bool := fun i => if p = i then true else x i
  let W := C.wires (List.ofFn x)
  let V := C.wires (List.ofFn y)
  let L := C.lineDegrees 14 {p.val}
  have hvalid (i : ℕ) (hi : i < 14 + C.gates.length) :
      invariant (L.getD i 0) (W.getD i false) (V.getD i false) (d i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases hin : i < 14
      · let j : Fin 14 := ⟨i,hin⟩
        change invariant (L.getD i 0) (W.getD j.val false) (V.getD j.val false) (d j.val)
        rw [inputDegree C p i hin, inputValue C x j, inputValue C y j, hd j]
        by_cases h : p = j
        · have he : i = p.val := congrArg Fin.val h.symm
          simp [invariant, y, h, he]
        · have he : i ≠ p.val := fun he => h (Fin.ext he.symm)
          simp [invariant, y, h, he]
      · let j := i - 14
        have he : i = 14+j := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        have hget : C.gates[j]? = some C.gates[j] := by simp [hj]
        obtain ⟨hop, a, b, hinp, _, ha, hb⟩ := hg j _ hget
        have ia := ih a (by omega) (by omega)
        have ib := ih b (by omega) (by omega)
        change invariant ((C.lineDegrees 14 {p.val}).getD i 0)
          ((C.wires (List.ofFn x)).getD i false) ((C.wires (List.ofFn y)).getD i false) (d i)
        rw [he]
        rcases hop with hop | hop
        · have hw (z : Fin 14 → Bool) := valueAt C z j hj a b ha hb (· && ·)
              (by intro w; simp [gateValue, GateOp.eval, hop, hinp])
          rw [degreeAt C p j hj a b ha hb (· + ·)
              (by intro w; simp [Gate.lineDegree, hop, hinp]), hw x, hw y,
              (hgate j _ a b hget hinp).1 hop]
          exact and_step _ _ _ _ _ _ _ _ ia ib
        · have hw (z : Fin 14 → Bool) := valueAt C z j hj a b ha hb (· || ·)
              (by intro w; simp [gateValue, GateOp.eval, hop, hinp])
          rw [degreeAt C p j hj a b ha hb max
              (by intro w; simp [Gate.lineDegree, hop, hinp]), hw x, hw y,
              (hgate j _ a b hget hinp).2 hop]
          exact or_step _ _ _ _ _ _ _ _ ia ib
  have ho : C.output < 14 + C.gates.length := by
    by_contra! h
    have ht : V.getD C.output false = true := htrue
    change (scan gateValue C.gates (List.ofFn y)).getD C.output false = true at ht
    rw [List.getD_eq_default _ _ (by rw [scan_length, List.length_ofFn]; exact h)] at ht
    contradiction
  by_contra! h
  have hb : L.getD C.output 0 ≤ 1 := by
    change C.lineDeg 14 {p.val} ≤ 1
    omega
  have hout := (hvalid C.output ho).2 hb (show V.getD C.output false = true from htrue)
  change C.eval (List.ofFn x) = true ∨ d C.output = true at hout
  rcases hout with hf | hz
  · exact Bool.noConfusion (hfalse.symm.trans hf)
  · exact Bool.noConfusion (hzero.symm.trans hz)

end PEqualNP.Outside.L_meta_2227_aux

theorem PEqualNP.Outside.L_meta_2227 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ) → Bool) (x4 : ℕ → Bool), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) → (∀ (x6 : Fin (14 : ℕ)), x4 ↑x6 = Decidable.decide (x2 = x6)) → (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x1.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x7) = ((x1.wires (List.ofFn x3)).getD x9 Bool.false && x4 x10 || x4 x9 && (x1.wires (List.ofFn x3)).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x7) = (x4 x9 || x4 x10))) → x1.eval (List.ofFn x3) = Bool.false → x1.eval (List.ofFn fun (x9 : Fin (14 : ℕ)) => if x2 = x9 then Bool.true else x3 x9) = Bool.true → x4 x1.output = Bool.false → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} := by
  exact L_meta_2227_aux.result

