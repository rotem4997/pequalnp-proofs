import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9123

theorem tb (n a k : ℕ) (hn : n < 2 ^ k) (ha : k ≤ a) : n.testBit a = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) ha))

theorem L3 (n : ℕ) (hn : n < 1024) (a : ℕ) :
    (List.ofFn fun i : Fin 10 => n.testBit i.val).getD a false = n.testBit a := by
  by_cases h : a < 10
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (tb n a 10 (lt_of_lt_of_eq hn (by norm_num)) (by omega)).symm

theorem L1 (n : ℕ) (hn : n < 1024) (t : Bool) (o : ℕ) (ho : o ≠ 10) :
    ((List.ofFn fun i : Fin 10 => n.testBit i.val) ++ [t]).getD o false = n.testBit o := by
  by_cases h : o < 10
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    exact L3 n hn o
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (tb n o 10 (lt_of_lt_of_eq hn (by norm_num)) (by omega)).symm

theorem L2 (n : ℕ) (t : Bool) :
    ((List.ofFn fun i : Fin 10 => n.testBit i.val) ++ [t]).getD 10 false = t := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem clamp (n : ℕ) (hn : n < 1024) (a : ℕ) : n.testBit a = n.testBit (min a 10) := by
  by_cases h : a ≤ 10
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), tb n a 10 (lt_of_lt_of_eq hn (by norm_num)) (by omega),
      tb n 10 10 (lt_of_lt_of_eq hn (by norm_num)) le_rfl]

theorem pick : ∀ a b : Fin 11, ∃ n ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] : List ℕ),
    (n.testBit a.val || n.testBit b.val) = false := by
  decide

theorem small : ∀ n ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] : List ℕ), n < 1024 := by
  decide

end PEqualNP.Outside.L_meta_9123

theorem PEqualNP.Outside.L_meta_9123 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (18 : ℕ) →       x2.length ≤ (2 : ℕ) →         x1.gates = [] →           ∃ x7 ∈ [((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)],             have x8 : List Bool := List.ofFn fun (x8 : Fin (10 : ℕ)) => x7.1.testBit ↑x8;             x1.eval (x8 ++ [(List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x2).any id]) ≠ x7.2 := by
  intro C x2 _ _ hlen hg
  obtain ⟨gs, o⟩ := C
  simp only at hg
  subst hg
  have hev : ∀ y : List Bool, ({ gates := [], output := o } : PEqualNP.CircuitLowerBounds.Circuit).eval y = y.getD o false := fun y => rfl
  have hmem : ∀ n ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] : List ℕ),
      (n, true) ∈ ([((3 : ℕ), Bool.true), ((6 : ℕ), Bool.true), ((12 : ℕ), Bool.true), ((24 : ℕ), Bool.true), ((17 : ℕ), Bool.true), ((33 : ℕ), Bool.true), ((66 : ℕ), Bool.true), ((132 : ℕ), Bool.true), ((264 : ℕ), Bool.true), ((528 : ℕ), Bool.true), ((160 : ℕ), Bool.true), ((640 : ℕ), Bool.true), ((576 : ℕ), Bool.true), ((320 : ℕ), Bool.true), ((288 : ℕ), Bool.true), ((50 : ℕ), Bool.false), ((69 : ℕ), Bool.false), ((104 : ℕ), Bool.false), ((116 : ℕ), Bool.false), ((138 : ℕ), Bool.false), ((201 : ℕ), Bool.false), ((208 : ℕ), Bool.false), ((276 : ℕ), Bool.false), ((385 : ℕ), Bool.false), ((402 : ℕ), Bool.false), ((521 : ℕ), Bool.false), ((548 : ℕ), Bool.false), ((554 : ℕ), Bool.false), ((770 : ℕ), Bool.false), ((773 : ℕ), Bool.false)] : List (ℕ × Bool)) := by
    decide
  by_cases ho : o = 10
  · subst ho
    have key : ∀ a b : ℕ, ∃ n ∈ ([3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288] : List ℕ),
        n < 1024 ∧ n.testBit a = false ∧ n.testBit b = false := by
      intro a b
      obtain ⟨n, hn, hab⟩ := PEqualNP.Outside.L_meta_9123.pick ⟨min a 10, by omega⟩ ⟨min b 10, by omega⟩
      have hs := PEqualNP.Outside.L_meta_9123.small n hn
      refine ⟨n, hn, hs, ?_, ?_⟩
      · rw [PEqualNP.Outside.L_meta_9123.clamp n hs a]
        simp only [Bool.or_eq_false_iff] at hab
        exact hab.1
      · rw [PEqualNP.Outside.L_meta_9123.clamp n hs b]
        simp only [Bool.or_eq_false_iff] at hab
        exact hab.2
    rcases x2 with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · refine ⟨(3, true), by decide, ?_⟩
      dsimp only
      rw [hev, PEqualNP.Outside.L_meta_9123.L2]
      simp
    · obtain ⟨n, hn, hs, ha, _⟩ := key a a
      refine ⟨(n, true), hmem n hn, ?_⟩
      dsimp only
      rw [hev, PEqualNP.Outside.L_meta_9123.L2]
      simp only [PEqualNP.Outside.L_meta_9123.L3 n hs, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, ha]
      decide
    · obtain ⟨n, hn, hs, ha, hb⟩ := key a b
      refine ⟨(n, true), hmem n hn, ?_⟩
      dsimp only
      rw [hev, PEqualNP.Outside.L_meta_9123.L2]
      simp only [PEqualNP.Outside.L_meta_9123.L3 n hs, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, ha, hb]
      decide
    · simp only [List.length_cons] at hlen
      omega
  · by_cases h1 : o ≤ 1
    · refine ⟨(12, true), by decide, ?_⟩
      dsimp only
      rw [hev, PEqualNP.Outside.L_meta_9123.L1 12 (by norm_num) _ o ho]
      interval_cases o <;> decide
    · refine ⟨(3, true), by decide, ?_⟩
      dsimp only
      rw [hev, PEqualNP.Outside.L_meta_9123.L1 3 (by norm_num) _ o ho,
        PEqualNP.Outside.L_meta_9123.tb 3 o 2 (by norm_num) (by omega)]
      decide
