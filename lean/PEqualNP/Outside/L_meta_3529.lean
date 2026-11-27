import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3529

def A : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]

def E (y : Fin 14 → Bool) : Prop :=
  ∃ (p : Fin 14) (q : Fin 14), (A.getD p.val 0).testBit q.val = true ∧ y p = true ∧ y q = true

def R : List ℕ := [129, 130, 136, 257, 260, 320, 514, 544, 576, 1025, 1040, 1056, 2056, 2064,
  2112, 4100, 4104, 4128, 8194, 8196, 8208, 127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290,
  1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297,
  8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256]

def row (k : Fin 58) (i : Fin 14) : Bool := (R.getD k.val 0).testBit i.val

set_option maxRecDepth 100000 in
theorem edges : ∀ p q : Fin 14, (A.getD p.val 0).testBit q.val = true →
    ∃ k : Fin 58, k.val < 21 ∧ ∀ i : Fin 14, decide (i = p ∨ i = q) = row k i := by
  decide

set_option maxRecDepth 100000 in
theorem bits : ∀ p q : Fin 14, (A.getD p.val 0).testBit q.val = true → p.val < 7 ∧ 7 ≤ q.val := by
  decide

theorem part1 (x : Fin 14 → Bool) (h : Minimal E x) :
    ∃ k : Fin 58, k.val < 21 ∧ x = fun i => row k i := by
  obtain ⟨⟨p, q, hpq, hp, hq⟩, hmin⟩ := h
  have hy : E (fun i => decide (i = p ∨ i = q)) := ⟨p, q, hpq, by simp, by simp⟩
  have hle : (fun i => decide (i = p ∨ i = q)) ≤ x := by
    intro i
    by_cases hi : i = p ∨ i = q
    · rcases hi with rfl | rfl
      · simp [hp]
      · simp [hq]
    · simp [hi]
  have hge : x ≤ (fun i => decide (i = p ∨ i = q)) := hmin hy hle
  obtain ⟨k, hk, hrow⟩ := edges p q hpq
  refine ⟨k, hk, ?_⟩
  funext i
  rw [← hrow i]
  exact le_antisymm (hge i) (hle i)

theorem flipE (x : Fin 14 → Bool) (h : Maximal (fun y => ¬ E y) x) (i : Fin 14)
    (hi : x i = false) : E (Function.update x i true) := by
  by_contra hne
  have hle : x ≤ Function.update x i true := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [hi]
    · simp [Function.update_of_ne hj]
  have := h.2 hne hle i
  simp [hi] at this
  exact absurd this (by decide : ¬ (true ≤ false))

def lv (c : Fin 7 → Bool) (l : Fin 14) : Bool :=
  (List.finRange 7).all (fun p => !((A.getD p.val 0).testBit l.val && c p))

def g (c : Fin 7 → Bool) (i : Fin 14) : Bool := if h : i.val < 7 then c ⟨i.val, h⟩ else lv c i

theorem cast_eq (p : Fin 14) (h : p.val < 7) : Fin.castLE (by norm_num) (⟨p.val, h⟩ : Fin 7) = p :=
  Fin.ext rfl

theorem lineEq (x : Fin 14 → Bool) (hx : ¬ E x) (hf : ∀ i, x i = false → E (Function.update x i true))
    (i : Fin 14) (hi : 7 ≤ i.val) :
    x i = lv (fun j : Fin 7 => x (Fin.castLE (by norm_num) j)) i := by
  rw [Bool.eq_iff_iff]
  simp only [lv, List.all_eq_true, List.mem_finRange, true_implies, Bool.not_eq_true',
    Bool.and_eq_false_iff]
  constructor
  · intro hxi p
    by_cases hb : (A.getD p.val 0).testBit i.val = true
    · right
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hx ⟨Fin.castLE (by norm_num) p, i, hb, hc, hxi⟩
    · left; simpa using hb
  · intro H
    by_contra hxi
    simp only [Bool.not_eq_true] at hxi
    obtain ⟨p', q', hadj, hp', hq'⟩ := hf i hxi
    obtain ⟨h1, h2⟩ := bits p' q' hadj
    have hne : p' ≠ i := fun e => by rw [e] at h1; omega
    rw [Function.update_of_ne hne] at hp'
    by_cases hq : q' = i
    · rw [hq] at hadj
      rcases H ⟨p'.val, h1⟩ with h | h
      · have h' : (A.getD p'.val 0).testBit i.val = false := h
        rw [hadj] at h'; cases h'
      · rw [cast_eq p' h1, hp'] at h; cases h
    · rw [Function.update_of_ne hq] at hq'
      exact hx ⟨p', q', hadj, hp', hq'⟩

theorem ptEq (x : Fin 14 → Bool) (hx : ¬ E x) (hf : ∀ i, x i = false → E (Function.update x i true))
    (p : Fin 14) (hp : p.val < 7) (hxp : x p = false) :
    ∃ l : Fin 14, (A.getD p.val 0).testBit l.val = true ∧ x l = true := by
  obtain ⟨p', q', hadj, hp', hq'⟩ := hf p hxp
  obtain ⟨h1, h2⟩ := bits p' q' hadj
  have hne : q' ≠ p := fun e => by rw [e] at h2; omega
  rw [Function.update_of_ne hne] at hq'
  by_cases he : p' = p
  · subst he; exact ⟨q', hadj, hq'⟩
  · rw [Function.update_of_ne he] at hp'
    exact absurd ⟨p', q', hadj, hp', hq'⟩ hx

set_option maxRecDepth 100000 in
theorem finChk : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (∀ p : Fin 7, (![b0, b1, b2, b3, b4, b5, b6] : Fin 7 → Bool) p = false →
      ∃ l : Fin 14, (A.getD p.val 0).testBit l.val = true ∧
        g ![b0, b1, b2, b3, b4, b5, b6] l = true) →
    ∃ k : Fin 58, 21 ≤ k.val ∧ ∀ i : Fin 14, g ![b0, b1, b2, b3, b4, b5, b6] i = row k i := by
  decide

theorem part2 (x : Fin 14 → Bool) (h : Maximal (fun y => ¬ E y) x) :
    ∃ k : Fin 58, 21 ≤ k.val ∧ x = fun i => row k i := by
  have hx : ¬ E x := h.1
  have hf : ∀ i, x i = false → E (Function.update x i true) := fun i hi => flipE x h i hi
  set c : Fin 7 → Bool := fun j => x (Fin.castLE (by norm_num) j) with hcdef
  have hxg : x = g c := by
    funext i
    unfold g
    split_ifs with hi
    · show x i = x (Fin.castLE _ ⟨i.val, hi⟩)
      rw [cast_eq i hi]
    · exact lineEq x hx hf i (by omega)
  have hc : c = ![c 0, c 1, c 2, c 3, c 4, c 5, c 6] := by
    funext j; fin_cases j <;> rfl
  have hpt : ∀ p : Fin 7, (![c 0, c 1, c 2, c 3, c 4, c 5, c 6] : Fin 7 → Bool) p = false →
      ∃ l : Fin 14, (A.getD p.val 0).testBit l.val = true ∧
        g ![c 0, c 1, c 2, c 3, c 4, c 5, c 6] l = true := by
    intro p hp
    rw [← hc] at hp ⊢
    obtain ⟨l, hl, hxl⟩ := ptEq x hx hf (Fin.castLE (by norm_num) p) (by rw [Fin.val_castLE]; exact p.isLt) hp
    refine ⟨l, hl, ?_⟩
    rw [← hxg]; exact hxl
  obtain ⟨k, hk, hrow⟩ := finChk _ _ _ _ _ _ _ hpt
  refine ⟨k, hk, ?_⟩
  funext i
  rw [hxg, hc]
  exact hrow i

end PEqualNP.Outside.L_meta_3529

theorem PEqualNP.Outside.L_meta_3529 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD ↑x2 (0 : ℕ)).testBit ↑x3 = Bool.true ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; have x2 : Fin (58 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : Fin (58 : ℕ)) (x3 : Fin (14 : ℕ)) =>   ((have x4 : List ℕ :=             have x4 : List ℕ :=               have x4 : List ℕ :=                 have x4 : List ℕ := [(12353 : ℕ), (13504 : ℕ), (14849 : ℕ), (16256 : ℕ)];                 (9288 : ℕ) :: (9992 : ℕ) :: (10273 : ℕ) :: (10656 : ℕ) :: x4;               (5186 : ℕ) :: (6147 : ℕ) :: (7426 : ℕ) :: (8297 : ℕ) :: (8416 : ℕ) :: (8488 : ℕ) :: (8713 : ℕ) :: x4;             have x5 : List ℕ := (3078 : ℕ) :: (3716 : ℕ) :: (4179 : ℕ) :: (4304 : ℕ) :: (4370 : ℕ) :: (4625 : ℕ) :: (5008 : ℕ) :: x4;             (1220 : ℕ) :: (1290 : ℕ) :: (1548 : ℕ) :: (2087 : ℕ) :: (2212 : ℕ) :: (2338 : ℕ) :: (2565 : ℕ) :: x5;           have x5 : List ℕ :=             have x5 : List ℕ :=               have x5 : List ℕ := (541 : ℕ) :: (660 : ℕ) :: (792 : ℕ) :: (1102 : ℕ) :: x4;               (127 : ℕ) :: (244 : ℕ) :: (314 : ℕ) :: (432 : ℕ) :: x5;             (2112 : ℕ) :: (4100 : ℕ) :: (4104 : ℕ) :: (4128 : ℕ) :: (8194 : ℕ) :: (8196 : ℕ) :: (8208 : ℕ) :: x5;           have x6 : List ℕ := (544 : ℕ) :: (576 : ℕ) :: (1025 : ℕ) :: (1040 : ℕ) :: (1056 : ℕ) :: (2056 : ℕ) :: (2064 : ℕ) :: x5;           (129 : ℕ) :: (130 : ℕ) :: (136 : ℕ) :: (257 : ℕ) :: (260 : ℕ) :: (320 : ℕ) :: (514 : ℕ) :: x6).getD         ↑x2 (0 : ℕ)).testBit     ↑x3; ∀ (x3 : Fin (14 : ℕ) → Bool), (Minimal x1 x3 → ∃ (x5 : Fin (58 : ℕ)), ↑x5 < (21 : ℕ) ∧ x3 = x2 x5) ∧ (Maximal (fun (x4 : Fin (14 : ℕ) → Bool) => ¬x1 x4) x3 → ∃ (x5 : Fin (58 : ℕ)), (21 : ℕ) ≤ ↑x5 ∧ x3 = x2 x5) := by
  intro x1 x2 x3
  exact ⟨fun h => PEqualNP.Outside.L_meta_3529.part1 x3 h, fun h => PEqualNP.Outside.L_meta_3529.part2 x3 h⟩
