import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_6076

def wst (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def cgates : List Gate :=
  [{ op := GateOp.or, inputs := [1, 2] },
   { op := GateOp.or, inputs := [26, 4] },
   { op := GateOp.or, inputs := [27, 10] },
   { op := GateOp.and, inputs := [28, 14] },
   { op := GateOp.or, inputs := [2, 3] },
   { op := GateOp.or, inputs := [30, 5] },
   { op := GateOp.or, inputs := [31, 11] },
   { op := GateOp.and, inputs := [32, 15] },
   { op := GateOp.or, inputs := [3, 4] },
   { op := GateOp.or, inputs := [34, 6] },
   { op := GateOp.or, inputs := [35, 12] },
   { op := GateOp.and, inputs := [36, 16] },
   { op := GateOp.or, inputs := [4, 5] },
   { op := GateOp.or, inputs := [38, 7] },
   { op := GateOp.or, inputs := [39, 0] },
   { op := GateOp.and, inputs := [40, 17] },
   { op := GateOp.or, inputs := [5, 6] },
   { op := GateOp.or, inputs := [42, 8] },
   { op := GateOp.or, inputs := [43, 1] },
   { op := GateOp.and, inputs := [44, 18] },
   { op := GateOp.or, inputs := [6, 7] },
   { op := GateOp.or, inputs := [46, 9] },
   { op := GateOp.or, inputs := [47, 2] },
   { op := GateOp.and, inputs := [48, 19] },
   { op := GateOp.or, inputs := [7, 8] },
   { op := GateOp.or, inputs := [50, 10] },
   { op := GateOp.or, inputs := [51, 3] },
   { op := GateOp.and, inputs := [52, 20] },
   { op := GateOp.or, inputs := [8, 9] },
   { op := GateOp.or, inputs := [54, 11] },
   { op := GateOp.or, inputs := [55, 4] },
   { op := GateOp.and, inputs := [56, 21] },
   { op := GateOp.or, inputs := [9, 10] },
   { op := GateOp.or, inputs := [58, 12] },
   { op := GateOp.or, inputs := [59, 5] },
   { op := GateOp.and, inputs := [60, 22] },
   { op := GateOp.or, inputs := [10, 11] },
   { op := GateOp.or, inputs := [62, 0] },
   { op := GateOp.or, inputs := [63, 6] },
   { op := GateOp.and, inputs := [64, 23] },
   { op := GateOp.or, inputs := [11, 12] },
   { op := GateOp.or, inputs := [66, 1] },
   { op := GateOp.or, inputs := [67, 7] },
   { op := GateOp.and, inputs := [68, 24] },
   { op := GateOp.or, inputs := [12, 0] },
   { op := GateOp.or, inputs := [70, 2] },
   { op := GateOp.or, inputs := [71, 8] },
   { op := GateOp.and, inputs := [72, 25] },
   { op := GateOp.or, inputs := [29, 33] },
   { op := GateOp.or, inputs := [74, 37] },
   { op := GateOp.or, inputs := [75, 41] },
   { op := GateOp.or, inputs := [76, 45] },
   { op := GateOp.or, inputs := [77, 49] },
   { op := GateOp.or, inputs := [78, 53] },
   { op := GateOp.or, inputs := [79, 57] },
   { op := GateOp.or, inputs := [80, 61] },
   { op := GateOp.or, inputs := [81, 65] },
   { op := GateOp.or, inputs := [82, 69] },
   { op := GateOp.or, inputs := [83, 73] },
   { op := GateOp.or, inputs := [0, 1] },
   { op := GateOp.or, inputs := [85, 3] },
   { op := GateOp.or, inputs := [86, 9] },
   { op := GateOp.or, inputs := [87, 84] },
   { op := GateOp.or, inputs := [13, 84] },
   { op := GateOp.and, inputs := [88, 89] }]

def cc : Circuit := { gates := cgates, output := 90 }

def vv (x7 : Fin 26 → Bool) (i : ℕ) : Bool := (List.foldl wst (List.ofFn x7) cgates).getD i false

theorem pref : ∀ (gs : List Gate) (w : List Bool),
    ∃ T : List Bool, List.foldl wst w gs = w ++ T ∧ T.length = gs.length
  | [], w => ⟨[], by simp, rfl⟩
  | g :: rest, w => by
    obtain ⟨T, hT, hl⟩ := pref rest (wst w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: T, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hT]
    simp [wst]

theorem getD_left (v t : List Bool) (o : ℕ) (h : o < v.length) :
    (v ++ t).getD o false = v.getD o false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_last (v : List Bool) (x : Bool) : (v ++ [x]).getD v.length false = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem ofFn_getD (n : ℕ) (f : Fin n → Bool) (T : List Bool) (i : ℕ) (h : i < n) :
    (List.ofFn f ++ T).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h),
    List.getElem?_eq_getElem (by simpa using h)]
  simp

theorem in_eq (gs : List Gate) (n : ℕ) (f : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.foldl wst (List.ofFn f) gs).getD i false = f ⟨i, h⟩ := by
  obtain ⟨T, hT, _⟩ := pref gs (List.ofFn f)
  rw [hT]
  exact ofFn_getD n f T i h

theorem wire_eq : ∀ (gs : List Gate) (w : List Bool) (n : ℕ), w.length = n →
    (∀ k (hk : k < gs.length), ∀ i ∈ gs[k].inputs, i < n + k) →
    ∀ k (hk : k < gs.length), (List.foldl wst w gs).getD (n + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (List.foldl wst w gs).getD i false)
  | [], _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | g :: rest, w, n, hn, hRB, k, hk => by
    have hlen : (wst w g).length = n + 1 := by simp [wst, hn]
    obtain ⟨T, hT, _⟩ := pref rest (wst w g)
    cases k with
    | zero =>
      have h0 : ∀ i ∈ g.inputs, i < n + 0 := hRB 0 (Nat.zero_lt_succ _)
      show (List.foldl wst (wst w g) rest).getD (n + 0) false =
        g.op.eval (g.inputs.map fun i => (List.foldl wst (wst w g) rest).getD i false)
      rw [hT]
      have e1 : (wst w g ++ T).getD (n + 0) false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [getD_left _ _ _ (by rw [hlen]; omega)]
        unfold wst
        rw [Nat.add_zero, ← hn, getD_last]
      rw [e1]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hi2 : i < w.length := by
        have := h0 i hi
        omega
      rw [getD_left _ _ _ (by rw [hlen]; omega)]
      unfold wst
      rw [getD_left _ _ _ hi2]
    | succ k =>
      have hk2 : k < rest.length := Nat.lt_of_succ_lt_succ hk
      have key := wire_eq rest (wst w g) (n + 1) hlen (fun j hj i hi => by
        have h1 : ∀ i ∈ rest[j].inputs, i < n + (j + 1) := hRB (j + 1) (Nat.succ_lt_succ hj)
        have := h1 i hi
        omega) k hk2
      have e2 : n + (k + 1) = n + 1 + k := by omega
      show (List.foldl wst (wst w g) rest).getD (n + (k + 1)) false =
        rest[k].op.eval (rest[k].inputs.map fun i => (List.foldl wst (wst w g) rest).getD i false)
      rw [e2]
      exact key

theorem wire_or (gs : List Gate) (w : List Bool) (n : ℕ) (hn : w.length = n)
    (hRB : ∀ k (hk : k < gs.length), ∀ i ∈ gs[k].inputs, i < n + k) (k : ℕ) (hk : k < gs.length) (a b : ℕ)
    (hg : gs[k] = { op := GateOp.or, inputs := [a, b] }) :
    (List.foldl wst w gs).getD (n + k) false =
      ((List.foldl wst w gs).getD a false || ((List.foldl wst w gs).getD b false || false)) := by
  rw [wire_eq gs w n hn hRB k hk, hg]
  rfl

theorem wire_and (gs : List Gate) (w : List Bool) (n : ℕ) (hn : w.length = n)
    (hRB : ∀ k (hk : k < gs.length), ∀ i ∈ gs[k].inputs, i < n + k) (k : ℕ) (hk : k < gs.length) (a b : ℕ)
    (hg : gs[k] = { op := GateOp.and, inputs := [a, b] }) :
    (List.foldl wst w gs).getD (n + k) false =
      ((List.foldl wst w gs).getD a false && ((List.foldl wst w gs).getD b false && true)) := by
  rw [wire_eq gs w n hn hRB k hk, hg]
  rfl

theorem term_false : ∀ (a b c d l : Bool), ¬(a = true ∧ l = true) → ¬(b = true ∧ l = true) →
    ¬(c = true ∧ l = true) → ¬(d = true ∧ l = true) →
    ((((a || (b || false)) || (c || false)) || (d || false)) && (l && true)) = false := by
  decide

theorem p0_false : ∀ (a b c d l : Bool), l = true → ¬(a = true ∧ l = true) → ¬(b = true ∧ l = true) →
    ¬(c = true ∧ l = true) → ¬(d = true ∧ l = true) →
    ((((a || (b || false)) || (c || false)) || (d || false)) || (false || false)) = false := by
  decide

theorem l_false : ∀ (l : Bool), ¬(l = true) → (l || (false || false)) = false := by
  decide

theorem hRBc : ∀ k (hk : k < cgates.length), ∀ i ∈ cgates[k].inputs, i < 26 + k := by
  decide +kernel

theorem both (x7 : Fin 26 → Bool)
    (hE : ∀ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → ¬(x7 (Fin.castAdd 13 p) = true ∧ x7 (Fin.natAdd 13 l) = true)) :
    (x7 (Fin.natAdd 13 (0 : Fin 13)) = true → vv x7 88 = false) ∧ (¬(x7 (Fin.natAdd 13 (0 : Fin 13)) = true) → vv x7 89 = false) := by
  have hl26 : (List.ofFn x7).length = 26 := by simp
  have i0 : vv x7 0 = x7 (Fin.castAdd 13 (0 : Fin 13)) := in_eq cgates 26 x7 0 (by decide)
  have i1 : vv x7 1 = x7 (Fin.castAdd 13 (1 : Fin 13)) := in_eq cgates 26 x7 1 (by decide)
  have i2 : vv x7 2 = x7 (Fin.castAdd 13 (2 : Fin 13)) := in_eq cgates 26 x7 2 (by decide)
  have i3 : vv x7 3 = x7 (Fin.castAdd 13 (3 : Fin 13)) := in_eq cgates 26 x7 3 (by decide)
  have i4 : vv x7 4 = x7 (Fin.castAdd 13 (4 : Fin 13)) := in_eq cgates 26 x7 4 (by decide)
  have i5 : vv x7 5 = x7 (Fin.castAdd 13 (5 : Fin 13)) := in_eq cgates 26 x7 5 (by decide)
  have i6 : vv x7 6 = x7 (Fin.castAdd 13 (6 : Fin 13)) := in_eq cgates 26 x7 6 (by decide)
  have i7 : vv x7 7 = x7 (Fin.castAdd 13 (7 : Fin 13)) := in_eq cgates 26 x7 7 (by decide)
  have i8 : vv x7 8 = x7 (Fin.castAdd 13 (8 : Fin 13)) := in_eq cgates 26 x7 8 (by decide)
  have i9 : vv x7 9 = x7 (Fin.castAdd 13 (9 : Fin 13)) := in_eq cgates 26 x7 9 (by decide)
  have i10 : vv x7 10 = x7 (Fin.castAdd 13 (10 : Fin 13)) := in_eq cgates 26 x7 10 (by decide)
  have i11 : vv x7 11 = x7 (Fin.castAdd 13 (11 : Fin 13)) := in_eq cgates 26 x7 11 (by decide)
  have i12 : vv x7 12 = x7 (Fin.castAdd 13 (12 : Fin 13)) := in_eq cgates 26 x7 12 (by decide)
  have i13 : vv x7 13 = x7 (Fin.natAdd 13 (0 : Fin 13)) := in_eq cgates 26 x7 13 (by decide)
  have i14 : vv x7 14 = x7 (Fin.natAdd 13 (1 : Fin 13)) := in_eq cgates 26 x7 14 (by decide)
  have i15 : vv x7 15 = x7 (Fin.natAdd 13 (2 : Fin 13)) := in_eq cgates 26 x7 15 (by decide)
  have i16 : vv x7 16 = x7 (Fin.natAdd 13 (3 : Fin 13)) := in_eq cgates 26 x7 16 (by decide)
  have i17 : vv x7 17 = x7 (Fin.natAdd 13 (4 : Fin 13)) := in_eq cgates 26 x7 17 (by decide)
  have i18 : vv x7 18 = x7 (Fin.natAdd 13 (5 : Fin 13)) := in_eq cgates 26 x7 18 (by decide)
  have i19 : vv x7 19 = x7 (Fin.natAdd 13 (6 : Fin 13)) := in_eq cgates 26 x7 19 (by decide)
  have i20 : vv x7 20 = x7 (Fin.natAdd 13 (7 : Fin 13)) := in_eq cgates 26 x7 20 (by decide)
  have i21 : vv x7 21 = x7 (Fin.natAdd 13 (8 : Fin 13)) := in_eq cgates 26 x7 21 (by decide)
  have i22 : vv x7 22 = x7 (Fin.natAdd 13 (9 : Fin 13)) := in_eq cgates 26 x7 22 (by decide)
  have i23 : vv x7 23 = x7 (Fin.natAdd 13 (10 : Fin 13)) := in_eq cgates 26 x7 23 (by decide)
  have i24 : vv x7 24 = x7 (Fin.natAdd 13 (11 : Fin 13)) := in_eq cgates 26 x7 24 (by decide)
  have i25 : vv x7 25 = x7 (Fin.natAdd 13 (12 : Fin 13)) := in_eq cgates 26 x7 25 (by decide)
  have e0 : vv x7 26 = (vv x7 1 || (vv x7 2 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 0 (by decide) 1 2 rfl
  have e1 : vv x7 27 = (vv x7 26 || (vv x7 4 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 1 (by decide) 26 4 rfl
  have e2 : vv x7 28 = (vv x7 27 || (vv x7 10 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 2 (by decide) 27 10 rfl
  have e3 : vv x7 29 = (vv x7 28 && (vv x7 14 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 3 (by decide) 28 14 rfl
  have e4 : vv x7 30 = (vv x7 2 || (vv x7 3 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 4 (by decide) 2 3 rfl
  have e5 : vv x7 31 = (vv x7 30 || (vv x7 5 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 5 (by decide) 30 5 rfl
  have e6 : vv x7 32 = (vv x7 31 || (vv x7 11 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 6 (by decide) 31 11 rfl
  have e7 : vv x7 33 = (vv x7 32 && (vv x7 15 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 7 (by decide) 32 15 rfl
  have e8 : vv x7 34 = (vv x7 3 || (vv x7 4 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 8 (by decide) 3 4 rfl
  have e9 : vv x7 35 = (vv x7 34 || (vv x7 6 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 9 (by decide) 34 6 rfl
  have e10 : vv x7 36 = (vv x7 35 || (vv x7 12 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 10 (by decide) 35 12 rfl
  have e11 : vv x7 37 = (vv x7 36 && (vv x7 16 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 11 (by decide) 36 16 rfl
  have e12 : vv x7 38 = (vv x7 4 || (vv x7 5 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 12 (by decide) 4 5 rfl
  have e13 : vv x7 39 = (vv x7 38 || (vv x7 7 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 13 (by decide) 38 7 rfl
  have e14 : vv x7 40 = (vv x7 39 || (vv x7 0 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 14 (by decide) 39 0 rfl
  have e15 : vv x7 41 = (vv x7 40 && (vv x7 17 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 15 (by decide) 40 17 rfl
  have e16 : vv x7 42 = (vv x7 5 || (vv x7 6 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 16 (by decide) 5 6 rfl
  have e17 : vv x7 43 = (vv x7 42 || (vv x7 8 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 17 (by decide) 42 8 rfl
  have e18 : vv x7 44 = (vv x7 43 || (vv x7 1 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 18 (by decide) 43 1 rfl
  have e19 : vv x7 45 = (vv x7 44 && (vv x7 18 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 19 (by decide) 44 18 rfl
  have e20 : vv x7 46 = (vv x7 6 || (vv x7 7 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 20 (by decide) 6 7 rfl
  have e21 : vv x7 47 = (vv x7 46 || (vv x7 9 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 21 (by decide) 46 9 rfl
  have e22 : vv x7 48 = (vv x7 47 || (vv x7 2 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 22 (by decide) 47 2 rfl
  have e23 : vv x7 49 = (vv x7 48 && (vv x7 19 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 23 (by decide) 48 19 rfl
  have e24 : vv x7 50 = (vv x7 7 || (vv x7 8 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 24 (by decide) 7 8 rfl
  have e25 : vv x7 51 = (vv x7 50 || (vv x7 10 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 25 (by decide) 50 10 rfl
  have e26 : vv x7 52 = (vv x7 51 || (vv x7 3 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 26 (by decide) 51 3 rfl
  have e27 : vv x7 53 = (vv x7 52 && (vv x7 20 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 27 (by decide) 52 20 rfl
  have e28 : vv x7 54 = (vv x7 8 || (vv x7 9 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 28 (by decide) 8 9 rfl
  have e29 : vv x7 55 = (vv x7 54 || (vv x7 11 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 29 (by decide) 54 11 rfl
  have e30 : vv x7 56 = (vv x7 55 || (vv x7 4 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 30 (by decide) 55 4 rfl
  have e31 : vv x7 57 = (vv x7 56 && (vv x7 21 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 31 (by decide) 56 21 rfl
  have e32 : vv x7 58 = (vv x7 9 || (vv x7 10 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 32 (by decide) 9 10 rfl
  have e33 : vv x7 59 = (vv x7 58 || (vv x7 12 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 33 (by decide) 58 12 rfl
  have e34 : vv x7 60 = (vv x7 59 || (vv x7 5 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 34 (by decide) 59 5 rfl
  have e35 : vv x7 61 = (vv x7 60 && (vv x7 22 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 35 (by decide) 60 22 rfl
  have e36 : vv x7 62 = (vv x7 10 || (vv x7 11 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 36 (by decide) 10 11 rfl
  have e37 : vv x7 63 = (vv x7 62 || (vv x7 0 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 37 (by decide) 62 0 rfl
  have e38 : vv x7 64 = (vv x7 63 || (vv x7 6 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 38 (by decide) 63 6 rfl
  have e39 : vv x7 65 = (vv x7 64 && (vv x7 23 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 39 (by decide) 64 23 rfl
  have e40 : vv x7 66 = (vv x7 11 || (vv x7 12 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 40 (by decide) 11 12 rfl
  have e41 : vv x7 67 = (vv x7 66 || (vv x7 1 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 41 (by decide) 66 1 rfl
  have e42 : vv x7 68 = (vv x7 67 || (vv x7 7 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 42 (by decide) 67 7 rfl
  have e43 : vv x7 69 = (vv x7 68 && (vv x7 24 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 43 (by decide) 68 24 rfl
  have e44 : vv x7 70 = (vv x7 12 || (vv x7 0 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 44 (by decide) 12 0 rfl
  have e45 : vv x7 71 = (vv x7 70 || (vv x7 2 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 45 (by decide) 70 2 rfl
  have e46 : vv x7 72 = (vv x7 71 || (vv x7 8 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 46 (by decide) 71 8 rfl
  have e47 : vv x7 73 = (vv x7 72 && (vv x7 25 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 47 (by decide) 72 25 rfl
  have e48 : vv x7 74 = (vv x7 29 || (vv x7 33 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 48 (by decide) 29 33 rfl
  have e49 : vv x7 75 = (vv x7 74 || (vv x7 37 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 49 (by decide) 74 37 rfl
  have e50 : vv x7 76 = (vv x7 75 || (vv x7 41 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 50 (by decide) 75 41 rfl
  have e51 : vv x7 77 = (vv x7 76 || (vv x7 45 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 51 (by decide) 76 45 rfl
  have e52 : vv x7 78 = (vv x7 77 || (vv x7 49 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 52 (by decide) 77 49 rfl
  have e53 : vv x7 79 = (vv x7 78 || (vv x7 53 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 53 (by decide) 78 53 rfl
  have e54 : vv x7 80 = (vv x7 79 || (vv x7 57 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 54 (by decide) 79 57 rfl
  have e55 : vv x7 81 = (vv x7 80 || (vv x7 61 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 55 (by decide) 80 61 rfl
  have e56 : vv x7 82 = (vv x7 81 || (vv x7 65 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 56 (by decide) 81 65 rfl
  have e57 : vv x7 83 = (vv x7 82 || (vv x7 69 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 57 (by decide) 82 69 rfl
  have e58 : vv x7 84 = (vv x7 83 || (vv x7 73 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 58 (by decide) 83 73 rfl
  have e59 : vv x7 85 = (vv x7 0 || (vv x7 1 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 59 (by decide) 0 1 rfl
  have e60 : vv x7 86 = (vv x7 85 || (vv x7 3 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 60 (by decide) 85 3 rfl
  have e61 : vv x7 87 = (vv x7 86 || (vv x7 9 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 61 (by decide) 86 9 rfl
  have e62 : vv x7 88 = (vv x7 87 || (vv x7 84 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 62 (by decide) 87 84 rfl
  have e63 : vv x7 89 = (vv x7 13 || (vv x7 84 || false)) := wire_or cgates (List.ofFn x7) 26 hl26 hRBc 63 (by decide) 13 84 rfl
  have e64 : vv x7 90 = (vv x7 88 && (vv x7 89 && true)) := wire_and cgates (List.ofFn x7) 26 hl26 hRBc 64 (by decide) 88 89 rfl
  have d1 : vv x7 29 = false := by
    rw [e3, e2, e1, e0, i1, i2, i4, i10, i14]
    exact term_false _ _ _ _ _ (hE 1 1 (by decide)) (hE 2 1 (by decide)) (hE 4 1 (by decide)) (hE 10 1 (by decide))
  have d2 : vv x7 33 = false := by
    rw [e7, e6, e5, e4, i2, i3, i5, i11, i15]
    exact term_false _ _ _ _ _ (hE 2 2 (by decide)) (hE 3 2 (by decide)) (hE 5 2 (by decide)) (hE 11 2 (by decide))
  have d3 : vv x7 37 = false := by
    rw [e11, e10, e9, e8, i3, i4, i6, i12, i16]
    exact term_false _ _ _ _ _ (hE 3 3 (by decide)) (hE 4 3 (by decide)) (hE 6 3 (by decide)) (hE 12 3 (by decide))
  have d4 : vv x7 41 = false := by
    rw [e15, e14, e13, e12, i4, i5, i7, i0, i17]
    exact term_false _ _ _ _ _ (hE 4 4 (by decide)) (hE 5 4 (by decide)) (hE 7 4 (by decide)) (hE 0 4 (by decide))
  have d5 : vv x7 45 = false := by
    rw [e19, e18, e17, e16, i5, i6, i8, i1, i18]
    exact term_false _ _ _ _ _ (hE 5 5 (by decide)) (hE 6 5 (by decide)) (hE 8 5 (by decide)) (hE 1 5 (by decide))
  have d6 : vv x7 49 = false := by
    rw [e23, e22, e21, e20, i6, i7, i9, i2, i19]
    exact term_false _ _ _ _ _ (hE 6 6 (by decide)) (hE 7 6 (by decide)) (hE 9 6 (by decide)) (hE 2 6 (by decide))
  have d7 : vv x7 53 = false := by
    rw [e27, e26, e25, e24, i7, i8, i10, i3, i20]
    exact term_false _ _ _ _ _ (hE 7 7 (by decide)) (hE 8 7 (by decide)) (hE 10 7 (by decide)) (hE 3 7 (by decide))
  have d8 : vv x7 57 = false := by
    rw [e31, e30, e29, e28, i8, i9, i11, i4, i21]
    exact term_false _ _ _ _ _ (hE 8 8 (by decide)) (hE 9 8 (by decide)) (hE 11 8 (by decide)) (hE 4 8 (by decide))
  have d9 : vv x7 61 = false := by
    rw [e35, e34, e33, e32, i9, i10, i12, i5, i22]
    exact term_false _ _ _ _ _ (hE 9 9 (by decide)) (hE 10 9 (by decide)) (hE 12 9 (by decide)) (hE 5 9 (by decide))
  have d10 : vv x7 65 = false := by
    rw [e39, e38, e37, e36, i10, i11, i0, i6, i23]
    exact term_false _ _ _ _ _ (hE 10 10 (by decide)) (hE 11 10 (by decide)) (hE 0 10 (by decide)) (hE 6 10 (by decide))
  have d11 : vv x7 69 = false := by
    rw [e43, e42, e41, e40, i11, i12, i1, i7, i24]
    exact term_false _ _ _ _ _ (hE 11 11 (by decide)) (hE 12 11 (by decide)) (hE 1 11 (by decide)) (hE 7 11 (by decide))
  have d12 : vv x7 73 = false := by
    rw [e47, e46, e45, e44, i12, i0, i2, i8, i25]
    exact term_false _ _ _ _ _ (hE 12 12 (by decide)) (hE 0 12 (by decide)) (hE 2 12 (by decide)) (hE 8 12 (by decide))
  have j0 : vv x7 74 = false := by
    rw [e48, d1, d2]
    rfl
  have j1 : vv x7 75 = false := by
    rw [e49, j0, d3]
    rfl
  have j2 : vv x7 76 = false := by
    rw [e50, j1, d4]
    rfl
  have j3 : vv x7 77 = false := by
    rw [e51, j2, d5]
    rfl
  have j4 : vv x7 78 = false := by
    rw [e52, j3, d6]
    rfl
  have j5 : vv x7 79 = false := by
    rw [e53, j4, d7]
    rfl
  have j6 : vv x7 80 = false := by
    rw [e54, j5, d8]
    rfl
  have j7 : vv x7 81 = false := by
    rw [e55, j6, d9]
    rfl
  have j8 : vv x7 82 = false := by
    rw [e56, j7, d10]
    rfl
  have j9 : vv x7 83 = false := by
    rw [e57, j8, d11]
    rfl
  have j10 : vv x7 84 = false := by
    rw [e58, j9, d12]
    rfl
  constructor
  · intro h13
    rw [e62, e61, e60, e59, j10, i0, i1, i3, i9]
    exact p0_false _ _ _ _ _ h13 (hE 0 0 (by decide)) (hE 1 0 (by decide)) (hE 3 0 (by decide)) (hE 9 0 (by decide))
  · intro h13
    rw [e63, j10, i13]
    exact l_false _ h13

theorem main : ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),
    x3.size ≤ 65 ∧ PEqualNP.TopForm.IsAO2 26 x3 ∧ (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧ x3.output = 26 + x4 ∧
    x3.gates[x4]? = Option.some { op := GateOp.and, inputs := [x5, x6] } ∧
    (∀ (x7 x8 : Fin 13), (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3 ∨ x7 = x8 + 9) →
      PEqualNP.BlindGate.wireValue x3 26 (fun (x10 : Fin 26) => Decidable.decide (x10 = Fin.castAdd 13 x7 ∨ x10 = Fin.natAdd 13 x8)) x5 = true ∧
      PEqualNP.BlindGate.wireValue x3 26 (fun (x10 : Fin 26) => Decidable.decide (x10 = Fin.castAdd 13 x7 ∨ x10 = Fin.natAdd 13 x8)) x6 = true) ∧
    ∀ (x7 : Fin 26 → Bool), Maximal (fun (x8 : Fin 26 → Bool) => ¬∃ (x3 : Fin 13) (x4 : Fin 13), (x3 = x4 ∨ x3 = x4 + 1 ∨ x3 = x4 + 3 ∨ x3 = x4 + 9) ∧ x8 (Fin.castAdd 13 x3) = true ∧ x8 (Fin.natAdd 13 x4) = true) x7 →
      PEqualNP.BlindGate.wireValue x3 26 x7 (if x7 13 = true then x5 else x6) = false := by
  refine ⟨cc, 64, 88, 89, by decide, by decide +kernel, by decide +kernel, rfl, rfl, by decide +kernel, ?_⟩
  intro x7 hmax
  have hI := hmax.prop
  have hb := both x7 (fun p l hpl hc => hI ⟨p, l, hpl, hc.1, hc.2⟩)
  by_cases h13 : x7 13 = true
  · rw [if_pos h13]
    exact hb.1 h13
  · rw [if_neg h13]
    exact hb.2 h13

end PEqualNP.Outside.L_meta_6076

theorem PEqualNP.Outside.L_meta_6076 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (65 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false := by
  intro x1 x2
  exact PEqualNP.Outside.L_meta_6076.main
