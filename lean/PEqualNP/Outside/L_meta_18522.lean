import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18522

def A : List ℕ := [10368, 4480, 8960, 1664, 3328, 6656, 13312]

def E (y : Fin 14 → Bool) : Prop :=
  ∃ (p : Fin 14) (q : Fin 14), (A.getD p.val 0).testBit q.val = true ∧ y p = true ∧ y q = true

def F (y : Fin 14 → Bool) : Prop :=
  ∃ (a : Fin 7) (b : Fin 7), (a = b ∨ a = b + 1 ∨ a = b + 3) ∧
    y (Fin.castAdd 7 a) = true ∧ y (Fin.natAdd 7 b) = true

def TL : List ℕ := [127, 244, 361, 480, 595, 720, 833, 1063, 1188, 1313, 1539, 2126, 2244, 2376,
  2626, 3008, 3078, 4125, 4244, 4361, 4625, 5125, 5889, 6156, 7300, 8250, 8368, 8488, 8722, 9250,
  9632, 10250, 11778, 12312, 12944, 14600, 16256]

set_option maxRecDepth 100000 in
theorem fwd : ∀ a b : Fin 7, (a = b ∨ a = b + 1 ∨ a = b + 3) →
    (A.getD a.val 0).testBit (7 + b.val) = true := by
  decide

set_option maxRecDepth 100000 in
theorem bwd : ∀ p q : Fin 14, (A.getD p.val 0).testBit q.val = true →
    ∃ a b : Fin 7, (a = b ∨ a = b + 1 ∨ a = b + 3) ∧ a.val = p.val ∧ 7 + b.val = q.val := by
  decide

theorem FE (y : Fin 14 → Bool) : F y ↔ E y := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨Fin.castAdd 7 a, Fin.natAdd 7 b, fwd a b hab, ha, hb⟩
  · rintro ⟨p, q, hpq, hp, hq⟩
    obtain ⟨a, b, hab, ha, hb⟩ := bwd p q hpq
    have e1 : Fin.castAdd 7 a = p := Fin.ext ha
    have e2 : Fin.natAdd 7 b = q := Fin.ext hb
    refine ⟨a, b, hab, ?_, ?_⟩
    · rw [e1]; exact hp
    · rw [e2]; exact hq

set_option maxRecDepth 100000 in
theorem bits : ∀ p q : Fin 14, (A.getD p.val 0).testBit q.val = true → p.val < 7 ∧ 7 ≤ q.val := by
  decide

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
    ∃ v ∈ TL, ∀ i : Fin 14, g ![b0, b1, b2, b3, b4, b5, b6] i = v.testBit i.val := by
  decide

theorem part2 (x : Fin 14 → Bool) (h : Maximal (fun y => ¬ E y) x) :
    ∃ v ∈ TL, ∀ i : Fin 14, x i = v.testBit i.val := by
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
  obtain ⟨v, hv, hrow⟩ := finChk _ _ _ _ _ _ _ hpt
  refine ⟨v, hv, fun i => ?_⟩
  rw [hxg, hc]
  exact hrow i

theorem main (x : Fin 14 → Bool) (h : Maximal (fun y => ¬ F y) x) :
    ∃ v ∈ TL, ∀ i : Fin 14, x i = v.testBit i.val := by
  have hfe : (fun y => ¬ F y) = (fun y => ¬ E y) := funext fun y => by rw [FE]
  rw [hfe] at h
  exact part2 x h

end PEqualNP.Outside.L_meta_18522

theorem PEqualNP.Outside.L_meta_18522 : ∀ (x1 : Fin (14 : ℕ) → Bool),   Maximal (fun (x2 : Fin (14 : ℕ) → Bool) => ¬∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) x1 →     ∃       x3 ∈         have x4 : List ℕ :=           have x4 : List ℕ :=             have x4 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];             (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x4;           have x5 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x4;           (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x5;         have x5 : List ℕ :=           have x5 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x4;           (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x5;         have x6 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x5;         (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x6,       ∀ (x4 : Fin (14 : ℕ)), x1 x4 = x3.testBit ↑x4 := by
  intro x hx
  exact PEqualNP.Outside.L_meta_18522.main x hx
