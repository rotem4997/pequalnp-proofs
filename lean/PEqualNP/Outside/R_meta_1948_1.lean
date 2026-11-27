import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1948_1 (h1 : ∃ (q N : ℕ) (I : Fin N → Fin N → Prop) (_ : DecidableRel I), 201 ≤ q ∧ N = q ^ 2 + q + 1 ∧ (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) ∧ (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)) (h2 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 201 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∧ PEqualNP.ReadK.IsReadK (N + N) C 2 ∧ C.size ≤ 2 * N) : ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size) := by
  intro hU
  obtain ⟨q, N, I, decI, hq, hN, hlines, hpairs⟩ := h1
  letI : DecidableRel I := decI
  have lines' : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1 := by
    intro l
    simpa only [Fintype.card_subtype] using hlines l
  obtain ⟨C, hAO, hfun, hread, hsize⟩ := h2 q N I hq hN hlines hpairs
  have hle := hU q N I C (by omega) hN lines' hpairs hAO hfun hread
  have hNpos : 0 < N := by
    rw [hN]
    positivity
  have hsmall : 100 * C.size ≤ 200 * N := by
    calc
      100 * C.size ≤ 100 * (2 * N) := Nat.mul_le_mul_left 100 hsize
      _ = 200 * N := by ring
  have hstep1 : 200 * N < 201 * N := by
    nlinarith
  have hstep2 : 201 * N ≤ q * N := Nat.mul_le_mul_right N hq
  have hbig : 200 * N < N * q := by
    calc
      200 * N < 201 * N := hstep1
      _ ≤ q * N := hstep2
      _ = N * q := by rw [Nat.mul_comm]
  omega
