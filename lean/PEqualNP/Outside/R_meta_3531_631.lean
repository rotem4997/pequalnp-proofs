import Mathlib
import PEqualNP.Defs

-- The last two packed operands are computed independently from a shared initial gate list.
theorem PEqualNP.Outside.R_meta_3531_631
    (bank : have x1 : List ℕ → Bool × ℕ × ℕ → ℕ := fun (x1 : List ℕ) (x2 : Bool × ℕ × ℕ) => if x2.1 = Bool.true then x1.getD x2.2.1 (0 : ℕ) ||| x1.getD x2.2.2 (0 : ℕ) else x1.getD x2.2.1 (0 : ℕ) &&& x1.getD x2.2.2 (0 : ℕ); ∃ (x2 : List (Bool × ℕ × ℕ)) (x3 : Bool × ℕ × ℕ) (x4 : Bool × ℕ × ℕ) (x5 : Fin (16 : ℕ)),   x2.length ≤ (23 : ℕ) ∧     have x6 : List ℕ := List.foldl (fun (x6 : List ℕ) (x7 : Bool × ℕ × ℕ) => x6 ++ [x1 x6 x7]) [(95229015649944073 : ℕ), (63038587928642 : ℕ), (256463372304 : ℕ), (4292497062825988 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (189297016294080519 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)] x2;     x4.2.1 < x6.length ∧       x4.2.2 < x6.length ∧         let x7 : ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)].getD ↑x5 (0 : ℕ);         let x8 : ℕ := x7 % (64 : ℕ);         have x9 : ℕ := x7 / (64 : ℕ);         have x10 : ℕ := x1 x6 x3;         have x11 : ℕ := x1 x6 x4;         (if x8 < (21 : ℕ) then x10 ||| x11 else x10 &&& x11) = (2097151 : ℕ) ∧ x10.testBit x8 ≠ x11.testBit x8 ∧ x10.testBit x8 = x11.testBit x9 ∧ x11.testBit x8 = x10.testBit x9)
    (stableRead : ∀ (w : List ℕ) (z i : ℕ), i < w.length →
      (w ++ [z]).getD i 0 = w.getD i 0) :
    ∃ (x1 : List (Bool × ℕ × ℕ)) (x2 : ℕ) (x3 : ℕ) (x4 : Fin (16 : ℕ)),   x1.length ≤ (25 : ℕ) ∧     (14 : ℕ) ≤ x2 ∧       x2 < x3 ∧         x3 < (14 : ℕ) + x1.length ∧           have x5 : ℕ := [(64 : ℕ), (256 : ℕ), (448 : ℕ), (1429 : ℕ), (1557 : ℕ), (2389 : ℕ), (3669 : ℕ), (1494 : ℕ), (1558 : ℕ), (1750 : ℕ), (1942 : ℕ), (2390 : ℕ), (2902 : ℕ), (1688 : ℕ), (1880 : ℕ), (2008 : ℕ)].getD ↑x4 (0 : ℕ);           have x6 : ℕ := x5 % (64 : ℕ);           have x7 : ℕ := x5 / (64 : ℕ);           have x8 : List ℕ := List.foldl (fun (x8 : List ℕ) (x9 : Bool × ℕ × ℕ) => x8 ++ [(fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)) x8 x9]) [(95229015649944073 : ℕ), (63038587928642 : ℕ), (256463372304 : ℕ), (4292497062825988 : ℕ), (8521482511360 : ℕ), (14003410187716736 : ℕ), (55389823206179104 : ℕ), (189297016294080519 : ℕ), (155696362464215096 : ℕ), (218994303131713984 : ℕ), (183565875465424384 : ℕ), (229736628136996864 : ℕ), (270286071508729856 : ℕ), (288160007409369088 : ℕ)] x1;           have x9 : ℕ := x8.getD x2 (0 : ℕ);           have x10 : ℕ := x8.getD x3 (0 : ℕ);           (if x6 < (21 : ℕ) then x9 ||| x10 else x9 &&& x10) = (2097151 : ℕ) ∧ x9.testBit x6 ≠ x10.testBit x6 ∧ x9.testBit x6 = x10.testBit x7 ∧ x10.testBit x6 = x9.testBit x7 := by
  let cols : List ℕ := [95229015649944073,63038587928642,256463372304,4292497062825988,8521482511360,14003410187716736,55389823206179104,189297016294080519,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088]
  let codes : List ℕ := [64,256,448,1429,1557,2389,3669,1494,1558,1750,1942,2390,2902,1688,1880,2008]
  let step (w : List ℕ) (g : Bool × ℕ × ℕ) : ℕ :=
    if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0
    else w.getD g.2.1 0 &&& w.getD g.2.2 0
  let run (gs : List (Bool × ℕ × ℕ)) : List ℕ :=
    gs.foldl (fun w g => w ++ [step w g]) cols
  have length (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) :
      (gs.foldl (fun w g => w ++ [step w g]) w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  obtain ⟨gs, g, h, s, hsize, hl, hr, hcut⟩ := bank
  let w := run gs
  have hl' : h.2.1 < w.length := hl
  have hr' : h.2.2 < w.length := hr
  have preserve : step (w ++ [step w g]) h = step w h := by
    simp only [step, stableRead w (step w g) _ hl', stableRead w (step w g) _ hr']
  let out := gs ++ [g, h]
  have outputLayout : run out = w ++ [step w g, step w h] := by
    change (gs ++ [g, h]).foldl (fun w g => w ++ [step w g]) cols = _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (w ++ [step w g]) ++ [step (w ++ [step w g]) h] = _
    rw [preserve, List.append_assoc]
    rfl
  have first : (run out).getD w.length 0 = step w g := by
    rw [outputLayout]
    simp [List.getD_eq_getElem?_getD]
  have second : (run out).getD (w.length + 1) 0 = step w h := by
    rw [outputLayout]
    simp [List.getD_eq_getElem?_getD]
  have wlen : w.length = 14 + gs.length := length gs cols
  have oLen : out.length = gs.length + 2 := by simp [out]
  refine ⟨out, w.length, w.length + 1, s, by omega, by omega, by omega, by omega, ?_⟩
  let i := (codes.getD s.val 0) % 64
  let j := (codes.getD s.val 0) / 64
  change
    (if i < 21 then (run out).getD w.length 0 ||| (run out).getD (w.length + 1) 0
      else (run out).getD w.length 0 &&& (run out).getD (w.length + 1) 0) = 2097151 ∧
    ((run out).getD w.length 0).testBit i ≠ ((run out).getD (w.length + 1) 0).testBit i ∧
    ((run out).getD w.length 0).testBit i = ((run out).getD (w.length + 1) 0).testBit j ∧
    ((run out).getD (w.length + 1) 0).testBit i = ((run out).getD w.length 0).testBit j
  rw [first, second]
  exact hcut
