import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1475_3
    (hmono : ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      Monotone (fun x : Fin 42 → Bool => C.eval (List.ofFn x)))
    (hcert :
      let E := fun (p l : Fin 21) => p = l ∨ p = l + 1 ∨ p = l + 4 ∨ p = l + 14 ∨ p = l + 16
      let Z := fun (y : Fin 21 → Bool) (l : Fin 21) =>
        !(y l || y (l + 1) || y (l + 4) || y (l + 14) || y (l + 16))
      ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧
        (∀ p l, E p l →
          C.eval (List.ofFn (Fin.addCases (fun i => decide (i = p))
            (fun i => decide (i = l)))) = true) ∧
        (∀ y, (∀ p, y p = false → ∃ l, E p l ∧ Z y l = true) →
          C.eval (List.ofFn (Fin.addCases y (Z y))) = false)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  classical
  let E (p l : Fin 21) := p = l ∨ p = l + 1 ∨ p = l + 4 ∨ p = l + 14 ∨ p = l + 16
  let Z (y : Fin 21 → Bool) (l : Fin 21) :=
    !(y l || y (l + 1) || y (l + 4) || y (l + 14) || y (l + 16))
  have hZ (y : Fin 21 → Bool) (l : Fin 21) :
      Z y l = true ↔ ∀ p, E p l → y p = false := by
    constructor
    · intro h p hp
      simp only [Z, Bool.not_eq_true', Bool.or_eq_false_iff] at h
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> tauto
    · intro h
      have h0 := h l (.inl rfl)
      have h1 := h (l + 1) (.inr (.inl rfl))
      have h4 := h (l + 4) (.inr (.inr (.inl rfl)))
      have h14 := h (l + 14) (.inr (.inr (.inr (.inl rfl))))
      have h16 := h (l + 16) (.inr (.inr (.inr (.inr rfl))))
      simp [Z, h0, h1, h4, h14, h16]
  obtain ⟨C, hmc, hsize, hedges, hclosed⟩ := hcert
  have hm := hmono C hmc
  have hcyclic : ∀ x : Fin 42 → Bool,
      C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 21, E p l ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true := by
    intro x
    constructor
    · intro hval
      by_contra hno
      -- Close the independent input by filling the compatible lines and then the compatible points.
      let y (p : Fin 21) := x (Fin.castAdd 21 p)
      let Y (p : Fin 21) := decide (∀ l, Z y l = true → ¬ E p l)
      have hyY (p : Fin 21) (hy : y p = true) : Y p = true := by
        simp only [Y, decide_eq_true_eq]
        intro l hl he
        have := (hZ y l).1 hl p he
        simp [hy] at this
      have hYZ (l : Fin 21) (hl : Z y l = true) : Z Y l = true := by
        apply (hZ Y l).2
        intro p hp
        by_contra h
        have h' : Y p = true := Bool.of_not_eq_false h
        exact (of_decide_eq_true h' l hl) hp
      have hZY (l : Fin 21) (hl : Z Y l = true) : Z y l = true := by
        apply (hZ y l).2
        intro p hp
        by_contra h
        have h' : y p = true := Bool.of_not_eq_false h
        have := (hZ Y l).1 hl p hp
        simp [hyY p h'] at this
      have hmax (p : Fin 21) (hp : Y p = false) : ∃ l, E p l ∧ Z Y l = true := by
        have h' : ¬ ∀ l, Z y l = true → ¬ E p l := of_decide_eq_false hp
        obtain ⟨l, hl⟩ := not_forall.mp h'
        obtain ⟨hzl, hel⟩ := not_imp.mp hl
        exact ⟨l, not_not.mp hel, hYZ l hzl⟩
      have hall : x ≤ Fin.addCases (motive := fun _ => Bool) Y (Z Y) := by
        intro i
        refine Fin.addCases (m := 21) (n := 21)
          (motive := fun j => x j ≤ Fin.addCases (motive := fun _ => Bool) Y (Z Y) j)
          ?_ ?_ i
        · intro p
          rw [Fin.addCases_left]
          change y p ≤ Y p
          cases hbit : y p with
          | false => simp
          | true => simp [hyY p hbit]
        · intro l
          rw [Fin.addCases_right]
          cases hbit : x (Fin.natAdd 21 l) with
          | false => exact Bool.false_le _
          | true =>
            have hz : Z y l = true := (hZ y l).2 (by
              intro p hp
              by_contra h
              have h' : y p = true := Bool.of_not_eq_false h
              exact hno ⟨p, l, hp, h', hbit⟩)
            simp only [hYZ l hz, Bool.le_true]
      have hle := hm hall
      dsimp only at hle
      rw [hval, hclosed Y hmax] at hle
      exact (by decide : ¬ true ≤ false) hle
    · rintro ⟨p, l, he, hp, hl⟩
      have hall : Fin.addCases (motive := fun _ => Bool)
          (fun i => decide (i = p)) (fun i => decide (i = l)) ≤ x := by
        intro i
        induction i using Fin.addCases with
        | left j =>
          rw [Fin.addCases_left]
          by_cases hj : j = p
          · simp only [hj, hp, Bool.le_true]
          · simp [hj]
        | right j =>
          rw [Fin.addCases_right]
          by_cases hj : j = l
          · simp only [hj, hl, Bool.le_true]
          · simp [hj]
      have hle := hm hall
      dsimp only at hle
      rw [hedges p l he] at hle
      exact Bool.eq_true_of_true_le hle
  let edges : List (ℕ × ℕ) := ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ))
  have hbounds : ∀ e ∈ edges, e.1 < 21 ∧ 21 ≤ e.2 ∧ e.2 < 42 := by decide
  have hrel : ∀ p l : Fin 21, (p.val, 21 + l.val) ∈ edges ↔ E p l := by decide
  refine ⟨C, hmc, hsize, ?_⟩
  intro x
  rw [hcyclic x]
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    exact ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, (hrel p l).mpr hpl, hp, hl⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    have hb := hbounds (u.val, v.val) huv
    let p : Fin 21 := ⟨u.val, hb.1⟩
    let l : Fin 21 := ⟨v.val - 21, by have := v.isLt; omega⟩
    have hp : Fin.castAdd 21 p = u := Fin.ext rfl
    have hl : Fin.natAdd 21 l = v := by apply Fin.ext; dsimp [l]; omega
    refine ⟨p, l, ?_, ?_, ?_⟩
    · apply (hrel p l).mp
      have heq : 21 + l.val = v.val := by dsimp [l]; omega
      simpa only [p, heq] using huv
    · simpa only [hp] using hu
    · simpa only [hl] using hv
