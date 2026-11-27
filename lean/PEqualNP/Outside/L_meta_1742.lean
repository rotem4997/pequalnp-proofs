import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1742

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

def G : List (Bool × ℕ × ℕ) := [(false, 0, 1), (false, 14, 2), (false, 7, 8), (false, 16, 9), (true, 15, 17), (false, 3, 4), (false, 19, 5), (false, 5, 6), (false, 4, 21), (true, 22, 10), (false, 3, 21), (true, 24, 11), (false, 19, 6), (true, 26, 12), (true, 20, 13), (false, 18, 23), (false, 29, 25), (false, 30, 27), (false, 31, 28)]

def Inc : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6), (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)]

def toGate (g : Bool × ℕ × ℕ) : Gate := ⟨cond g.1 GateOp.and GateOp.or, [g.2.1, g.2.2]⟩

def C0 : Circuit := ⟨G.map toGate, 32⟩

def stpG (fa fo : ℕ → ℕ → ℕ) (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [cond g.1 (fa (w.getD g.2.1 0) (w.getD g.2.2 0)) (fo (w.getD g.2.1 0) (w.getD g.2.2 0))]

def rd (n : ℕ) (r : List ℕ) (a : ℕ) : ℕ := if a < n then r.getD (n - 1 - a) 0 else 0

def evR (fa fo : ℕ → ℕ → ℕ) : List (Bool × ℕ × ℕ) → ℕ → List ℕ → List ℕ
  | [], _, r => r
  | g :: gs, n, r =>
    evR fa fo gs (n + 1)
      (cond g.1 (fa (rd n r g.2.1) (rd n r g.2.2)) (fo (rd n r g.2.1) (rd n r g.2.2)) :: r)

theorem rd_eq (w : List ℕ) (a : ℕ) : rd w.length w.reverse a = w.getD a 0 := by
  unfold rd
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 2
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem evR_eq (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    evR fa fo gs w.length w.reverse = (gs.foldl (stpG fa fo) w).reverse := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ← ih, evR, rd_eq, rd_eq]
    simp [stpG]

theorem length_fold (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (gs.foldl (stpG fa fo) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stpG]
    omega

theorem fold_getD (fa fo : ℕ → ℕ → ℕ) (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (a : ℕ) :
    (gs.foldl (stpG fa fo) w).getD a 0
      = rd (w.length + gs.length) (evR fa fo gs w.length w.reverse) a := by
  rw [evR_eq, ← length_fold fa fo, rd_eq]

def stpN (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ := stpG (fun a b => a &&& b) (fun a b => a ||| b) w g

theorem getD_tb (k : ℕ) (W : List ℕ) (i : ℕ) :
    (W.map fun v => v.testBit k).getD i false = (W.getD i 0).testBit k := by
  have h := List.getD_map (f := fun v : ℕ => v.testBit k) (l := W) (d := 0) (n := i)
  simpa using h

theorem bridge (k : ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (W : List ℕ),
    (gs.map toGate).foldl stp (W.map fun v => v.testBit k)
      = (gs.foldl stpN W).map fun v => v.testBit k := by
  intro gs
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    obtain ⟨b, i, j⟩ := g
    have hi := getD_tb k W i
    have hj := getD_tb k W j
    cases b
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_lor]
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_land]

def tab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => if p = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else tab n p ||| (tab n p <<< 2 ^ n)

theorem tab_bit : ∀ n p k, p < n →
    (tab n p).testBit k = (decide (k < 2 ^ n) && k.testBit p) := by
  intro n
  induction n with
  | zero => intro p k h; omega
  | succ n ih =>
    intro p k hp
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [tab]
    split_ifs with hpn
    · subst hpn
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hk : k < 2 ^ p
      · rw [Nat.testBit_lt_two_pow hk]
        simp
        omega
      · have hb : k.testBit p = !((k - 2 ^ p).testBit p) := by
          rw [← Nat.testBit_two_pow_add_eq]
          congr 1
          omega
        by_cases hk2 : k - 2 ^ p < 2 ^ p
        · have e0 : decide (k ≥ 2 ^ p) = true := by
            simp only [decide_eq_true_eq]
            omega
          have e1 : decide (k - 2 ^ p < 2 ^ p) = true := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = true := by
            simp only [decide_eq_true_eq]
            omega
          rw [hb, Nat.testBit_lt_two_pow hk2, e0, e1, e2]
          rfl
        · have e1 : decide (k - 2 ^ p < 2 ^ p) = false := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = false := by
            simp only [decide_eq_false_iff_not]
            omega
          rw [e1, e2]
          simp
    · have hp' : p < n := by omega
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih p k hp', ih p (k - 2 ^ n) hp']
      by_cases hk : k < 2 ^ n
      · have e1 : decide (k < 2 ^ n) = true := by simpa using hk
        have e2 : decide (k < 2 ^ (n + 1)) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e3 : decide (k ≥ 2 ^ n) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        rw [e1, e2, e3]
        simp
      · have hb : (k - 2 ^ n).testBit p = k.testBit p := by
          rw [← Nat.testBit_two_pow_add_gt hp' (k - 2 ^ n)]
          congr 1
          omega
        have e1 : decide (k < 2 ^ n) = false := by simpa using hk
        have e3 : decide (k ≥ 2 ^ n) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e4 : decide (k - 2 ^ n < 2 ^ n) = decide (k < 2 ^ (n + 1)) := by
          apply decide_eq_decide.mpr
          omega
        rw [e1, e3, e4, hb]
        simp

def W : List ℕ := (List.range 14).map (tab 14)

theorem W_getD (i : ℕ) : W.getD i 0 = if i < 14 then tab 14 i else 0 := by
  unfold W
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem W_len : W.length = 14 := by simp [W]

theorem G_len : G.length = 19 := by decide +kernel

def E : ℕ := Inc.foldr (fun q acc => (tab 14 q.1 &&& tab 14 (7 + q.2)) ||| acc) 0

set_option maxRecDepth 100000 in
theorem out0 :
    rd 33 (evR (fun a b => a &&& b) (fun a b => a ||| b) G 14 W.reverse) 32 = E := by
  decide +kernel

theorem out_eq : (G.foldl stpN W).getD 32 0 = E := by
  have h := fold_getD (fun a b => a &&& b) (fun a b => a ||| b) G W 32
  rw [W_len, G_len] at h
  exact h.trans out0

theorem any_bit (k : ℕ) (hk : k < 2 ^ 14) : ∀ L : List (ℕ × ℕ), (∀ q ∈ L, q.1 < 7 ∧ q.2 < 7) →
    (L.foldr (fun q acc => (tab 14 q.1 &&& tab 14 (7 + q.2)) ||| acc) 0).testBit k
      = L.any (fun q => k.testBit q.1 && k.testBit (7 + q.2)) := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons q L ih =>
    intro hL
    have hq := hL q List.mem_cons_self
    rw [List.foldr_cons, List.any_cons, Nat.testBit_lor, Nat.testBit_land,
      tab_bit 14 q.1 k (by omega), tab_bit 14 (7 + q.2) k (by omega),
      ih (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')), decide_eq_true hk]
    simp

theorem Inc_lt : ∀ q ∈ Inc, q.1 < 7 ∧ q.2 < 7 := by decide +kernel

theorem c1 : ∀ m : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun p : Fin 7 => ((p : ℕ), (m : ℕ)) ∈ Inc)).card = 3 := by
  decide +kernel

theorem c2 : ∀ p : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ Inc)).card = 3 := by
  decide +kernel

theorem c3 : ∀ p p' : Fin 7, p ≠ p' → ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ Inc ∧ ((p' : ℕ), (l : ℕ)) ∈ Inc)).card ≠ 1 := by
  decide +kernel

theorem len : C0.gates.length = 19 := by
  show (G.map toGate).length = 19
  rw [List.length_map, G_len]

theorem andOr : ∀ g ∈ C0.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [C0, List.mem_map] at hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := hg
  cases b
  · exact ⟨Or.inr rfl, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem readsG : ∀ j < 19, (G.getD j (false, 0, 0)).2.1 < 14 + j ∧ (G.getD j (false, 0, 0)).2.2 < 14 + j := by
  decide +kernel

theorem readsBack : PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C0 := by
  intro j hj i hi
  rw [len] at hj
  have h := readsG j hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C0 j = toGate (G.getD j (false, 0, 0)) := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    show (G.map toGate).getD j _ = _
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [G_len]; exact hj)]
    rfl
  rw [e] at hi
  simp only [toGate, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h.1
  · exact h.2

theorem inp_getD (x y : Fin 7 → Bool) (i : ℕ) :
    (List.ofFn x ++ List.ofFn y).getD i false =
      if h : i < 7 then x ⟨i, h⟩ else if h2 : i - 7 < 7 then y ⟨i - 7, h2⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < 7
  · rw [List.getElem?_append_left (by simpa using h), dif_pos h, ← List.getD_eq_getElem?_getD,
      ofFn_getD, dif_pos h]
  · rw [List.getElem?_append_right (by simpa using h), dif_neg h, ← List.getD_eq_getElem?_getD,
      ofFn_getD]
    simp

theorem main (x y : Fin 7 → Bool) :
    C0.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7,
      ((p : ℕ), (l : ℕ)) ∈ Inc ∧ x p = true ∧ y l = true) := by
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k < 2 ^ 14 ∧ ∀ (i : ℕ) (_ : i < 14), k.testBit i =
      if h : i < 7 then x ⟨i, h⟩ else if h2 : i - 7 < 7 then y ⟨i - 7, h2⟩ else false := by
    let z : Fin 14 → Bool := fun i =>
      if h : i.1 < 7 then x ⟨i.1, h⟩ else if h2 : i.1 - 7 < 7 then y ⟨i.1 - 7, h2⟩ else false
    exact ⟨Nat.ofBits z, Nat.ofBits_lt_two_pow z, fun i hi => Nat.testBit_ofBits_lt z i hi⟩
  have hx : ∀ (m : ℕ) (hm : m < 7), k.testBit m = x ⟨m, hm⟩ := by
    intro m hm
    rw [hk2 m (by omega), dif_pos hm]
  have hy : ∀ (m : ℕ) (hm : m < 7), k.testBit (7 + m) = y ⟨m, hm⟩ := by
    intro m hm
    rw [hk2 (7 + m) (by omega), dif_neg (by omega), dif_pos (show 7 + m - 7 < 7 by omega)]
    congr 1
    apply Fin.ext
    show 7 + m - 7 = m
    omega
  have hin : List.ofFn x ++ List.ofFn y = W.map (fun v => v.testBit k) := by
    refine List.ext_getElem (by simp [W]) (fun i h1 h2 => ?_)
    have h14 : i < 14 := by simpa using h1
    rw [← List.getD_eq_getElem _ false h1, ← List.getD_eq_getElem _ false h2, inp_getD, getD_tb,
      W_getD, if_pos h14, tab_bit 14 i k h14, decide_eq_true hk1, Bool.true_and, hk2 i h14]
  rw [eval_eq, hin]
  show ((G.map toGate).foldl stp (W.map fun v => v.testBit k)).getD 32 false = _
  rw [bridge, getD_tb, out_eq]
  show (Inc.foldr (fun q acc => (tab 14 q.1 &&& tab 14 (7 + q.2)) ||| acc) 0).testBit k = _
  rw [any_bit k hk1 Inc Inc_lt]
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hb⟩
    obtain ⟨h1, h2⟩ := Inc_lt q hq
    rw [Bool.and_eq_true, hx q.1 h1, hy q.2 h2] at hb
    exact ⟨⟨q.1, h1⟩, ⟨q.2, h2⟩, hq, hb.1, hb.2⟩
  · rintro ⟨p, l, hm, hx', hy'⟩
    refine ⟨(p.1, l.1), hm, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(hx p.1 p.2).trans hx', (hy l.1 l.2).trans hy'⟩

set_option maxRecDepth 100000 in
theorem full : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 28] }], output := 32 } : PEqualNP.CircuitLowerBounds.Circuit) →
  let B2 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6),
    (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)];
  (∀ m : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun p : Fin 7 => ((p : ℕ), (m : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p p' : Fin 7, p ≠ p' → ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2 ∧ ((p' : ℕ), (l : ℕ)) ∈ B2)).card ≠ 1) ∧
  C.gates.length = 19 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (x y : Fin 7 → Bool), C.eval (List.ofFn x ++ List.ofFn y)
     = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ B2 ∧ x p = true ∧ y l = true) := by
  intro C hC
  have hC' : C = C0 := hC
  clear hC
  subst hC'
  exact ⟨c1, c2, c3, len, readsBack, andOr, main⟩

end PEqualNP.Outside.L_meta_1742

theorem PEqualNP.Outside.L_meta_1742 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 28] }], output := 32 } : PEqualNP.CircuitLowerBounds.Circuit) →
  let B2 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6),
    (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)];
  (∀ m : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun p : Fin 7 => ((p : ℕ), (m : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p p' : Fin 7, p ≠ p' → ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2 ∧ ((p' : ℕ), (l : ℕ)) ∈ B2)).card ≠ 1) ∧
  C.gates.length = 19 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (x y : Fin 7 → Bool), C.eval (List.ofFn x ++ List.ofFn y)
     = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ B2 ∧ x p = true ∧ y l = true) := by
  exact PEqualNP.Outside.L_meta_1742.full
