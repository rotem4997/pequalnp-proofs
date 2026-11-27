import PEqualNP.Defs

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.R_meta_6670_137
    (seed : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 22 ∧
      ∀ x : Fin 13 → Bool, C.eval (List.ofFn x) = ((x 0 && x 7) || (x 0 && x 10) || (x 0 && x 12) || (x 1 && x 7) || (x 1 && x 11) || (x 2 && x 8) || (x 2 && x 12) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 9) || (x 4 && x 9) || (x 4 && x 10) || (x 5 && x 8) || (x 5 && x 10) || (x 5 && x 11) || (x 6 && x 9) || (x 6 && x 11) || (x 6 && x 12)))
    (normalize : ∀ (n m : ℕ) (e : Fin n → Fin m)
      (C : PEqualNP.CircuitLowerBounds.Circuit), Function.Injective e →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b) →
      (∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 m D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        m ≤ D.output ∧ D.output < m + D.size ∧ D.size ≤ C.size ∧
        ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), (x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ((∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x4 ≠ (1 : Fin (7 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → x1.eval (List.ofFn x2) = Bool.true)) := by
  obtain ⟨C, mono, size, correct⟩ := seed
  let f : (Fin 13 → Bool) → Bool := fun x => (x 0 && x 7) || (x 0 && x 10) || (x 0 && x 12) || (x 1 && x 7) || (x 1 && x 11) || (x 2 && x 8) || (x 2 && x 12) || (x 3 && x 7) || (x 3 && x 8) || (x 3 && x 9) || (x 4 && x 9) || (x 4 && x 10) || (x 5 && x 8) || (x 5 && x 10) || (x 5 && x 11) || (x 6 && x 9) || (x 6 && x 11) || (x 6 && x 12)
  change ∀ x : Fin 13 → Bool, C.eval (List.ofFn x) = f x at correct
  let e : Fin 13 → Fin 14 := fun i => Fin.ofNat 14 (if i.val < 8 then i.val else i.val + 1)
  have injective : Function.Injective e := by decide
  have e0 : e (0 : Fin 13) = (0 : Fin 14) := by decide
  have e1 : e (1 : Fin 13) = (1 : Fin 14) := by decide
  have e2 : e (2 : Fin 13) = (2 : Fin 14) := by decide
  have e3 : e (3 : Fin 13) = (3 : Fin 14) := by decide
  have e4 : e (4 : Fin 13) = (4 : Fin 14) := by decide
  have e5 : e (5 : Fin 13) = (5 : Fin 14) := by decide
  have e6 : e (6 : Fin 13) = (6 : Fin 14) := by decide
  have e7 : e (7 : Fin 13) = (7 : Fin 14) := by decide
  have e8 : e (8 : Fin 13) = (9 : Fin 14) := by decide
  have e9 : e (9 : Fin 13) = (10 : Fin 14) := by decide
  have e10 : e (10 : Fin 13) = (11 : Fin 14) := by decide
  have e11 : e (11 : Fin 13) = (12 : Fin 14) := by decide
  have e12 : e (12 : Fin 13) = (13 : Fin 14) := by decide
  have nonconstant : ∀ b : Bool, ∃ x : Fin 13 → Bool, C.eval (List.ofFn x) ≠ b := by
    intro b
    cases b
    · refine ⟨fun _ => true, ?_⟩
      rw [correct]
      decide
    · refine ⟨fun _ => false, ?_⟩
      rw [correct]
      decide
  have singletons : ∀ i : Fin 13, f (fun j => decide (j = i)) = false := by decide
  have not_input : ∀ i : Fin 13, ∃ x : Fin 13 → Bool, C.eval (List.ofFn x) ≠ x i := by
    intro i
    refine ⟨fun j => decide (j = i), ?_⟩
    rw [correct, singletons i]
    simp
  obtain ⟨D, ao, nodup, lo, hi, small, same⟩ :=
    normalize 13 14 e C injective mono nonconstant not_input
  have edges : ∀ x : Fin 14 → Bool, f (x ∘ e) = true ↔
      ∃ p l : Fin 7, l ≠ 1 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
    intro x
    simp [f, Function.comp_def, Fin.exists_fin_succ, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  refine ⟨D, small.trans size, ao, nodup, lo, hi, ?_⟩
  intro x
  rw [same x, correct]
  constructor
  · intro accepted
    obtain ⟨p, l, _, incident, hp, hl⟩ := (edges x).mp accepted
    exact ⟨p, l, incident, hp, hl⟩
  · intro required
    exact (edges x).mpr required
