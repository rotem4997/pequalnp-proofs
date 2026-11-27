import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9083_aux

theorem eval_nil (C : PEqualNP.CircuitLowerBounds.Circuit) (h : C.gates = [])
    (x : List Bool) : C.eval x = x.getD C.output false := by
  simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, h]

theorem getD_min (l : List Bool) (n : ℕ) (hl : l.length ≤ n) (a : ℕ) :
    l.getD a false = l.getD (min a n) false := by
  rcases lt_or_ge a n with h | h
  · rw [min_eq_left h.le]
  · rw [min_eq_right h, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

theorem aux0 : ∀ o < 12, ∃ x7 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],
    (List.ofFn (fun i : Fin 10 => x7.1.testBit i) ++ [([] : List Bool).all id]).getD o false ≠ x7.2 := by
  decide +kernel

theorem aux1 : ∀ o < 12, ∀ a < 11, ∃ x7 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],
    (List.ofFn (fun i : Fin 10 => x7.1.testBit i) ++
      [[(List.ofFn (fun i : Fin 10 => x7.1.testBit i)).getD a false].all id]).getD o false ≠ x7.2 := by
  decide +kernel

theorem aux2 : ∀ o < 12, ∀ a < 11, ∀ b < 11, ∃ x7 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],
    (List.ofFn (fun i : Fin 10 => x7.1.testBit i) ++
      [[(List.ofFn (fun i : Fin 10 => x7.1.testBit i)).getD a false,
        (List.ofFn (fun i : Fin 10 => x7.1.testBit i)).getD b false].all id]).getD o false ≠ x7.2 := by
  decide +kernel

end PEqualNP.Outside.L_meta_9083_aux

open PEqualNP.Outside.L_meta_9083_aux in
theorem PEqualNP.Outside.L_meta_9083 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         x1.gates = [] →           ∃ x7 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],             have x8 : List Bool := List.ofFn fun (x8 : Fin (10 : ℕ)) => x7.1.testBit ↑x8;             x1.eval (x8 ++ [(List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x2).all id]) ≠ x7.2 := by
  intro C x2 _ _ hlen hg
  match x2, hlen with
  | [], _ =>
    obtain ⟨x7, hm, h⟩ := aux0 (min C.output 11) (by omega)
    refine ⟨x7, hm, ?_⟩
    intro x8
    rw [eval_nil C hg, getD_min _ 11 (by simp [x8]) C.output]
    exact h
  | [a], _ =>
    obtain ⟨x7, hm, h⟩ := aux1 (min C.output 11) (by omega) (min a 10) (by omega)
    refine ⟨x7, hm, ?_⟩
    intro x8
    rw [eval_nil C hg, getD_min _ 11 (by simp [x8]) C.output]
    simp only [List.map_cons, List.map_nil]
    rw [getD_min x8 10 (by simp [x8]) a]
    exact h
  | [a, b], _ =>
    obtain ⟨x7, hm, h⟩ := aux2 (min C.output 11) (by omega) (min a 10) (by omega) (min b 10) (by omega)
    refine ⟨x7, hm, ?_⟩
    intro x8
    rw [eval_nil C hg, getD_min _ 11 (by simp [x8]) C.output]
    simp only [List.map_cons, List.map_nil]
    rw [getD_min x8 10 (by simp [x8]) a, getD_min x8 10 (by simp [x8]) b]
    exact h
  | _ :: _ :: _ :: _, h =>
    simp at h
