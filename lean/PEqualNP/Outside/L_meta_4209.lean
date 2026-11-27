import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4209

def L (a b : Fin 13) : Bool := decide (∃ c ∈ [(0 : Fin 13), 1, 3, 9], a = b + c)

def X (k : ℕ) (t a : Fin 13) : Bool := k.testBit (a - t).val

def Y (k : ℕ) (t a : Fin 13) : Bool := decide (∀ p : Fin 13, X k t p = true → L p a = false)

def P1 (k : ℕ) (t : Fin 13) : Bool :=
  decide (∀ p : Fin 13, X k t p = false → ∃ l : Fin 13, Y k t l = true ∧ L p l = true)

def P2 (k : ℕ) (t : Fin 13) : Bool :=
  decide (∃ l : Fin 13, ∀ p : Fin 13, X k t p = true → L p l = true)

def P3 (k : ℕ) (t : Fin 13) : Bool :=
  decide (∃ p : Fin 13, ∀ l : Fin 13, Y k t l = true → L p l = true)

theorem key : ∀ k ∈ [8191, 7668, 6624, 5584, 3492, 1408, 7492, 7316, 6272, 7472, 4176, 2084, 6144,
    5120, 4160, 2304, 2052, 4112, 4096, 0], ∀ t : Fin 13,
    P1 k t = true ∧ (P2 k t = true ∨ P3 k t = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_4209

open PEqualNP.Outside.L_meta_4209 in
theorem PEqualNP.Outside.L_meta_4209 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ∃ x3 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].toFinset, x1 = x2 + x3; ∀ (x2 : ℕ) (x3 : Fin (13 : ℕ)),   x2 ∈ [(8191 : ℕ), (7668 : ℕ), (6624 : ℕ), (5584 : ℕ), (3492 : ℕ), (1408 : ℕ), (7492 : ℕ), (7316 : ℕ), (6272 : ℕ), (7472 : ℕ), (4176 : ℕ), (2084 : ℕ), (6144 : ℕ), (5120 : ℕ), (4160 : ℕ), (2304 : ℕ), (2052 : ℕ), (4112 : ℕ), (4096 : ℕ), (0 : ℕ)].toFinset →     have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x2.testBit ↑(x5 - x3) = Bool.true};     have x6 : Fin (13 : ℕ) → Prop := fun (x6 : Fin (13 : ℕ)) => ∀ x7 ∈ x5, ¬x1 x7 x6;     (∀ x7 ∉ x5, ∃ (x9 : Fin (13 : ℕ)), x6 x9 ∧ x1 x7 x9) ∧ ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x1 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x6 x8 → x1 x7 x8) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  intro k t hk
  obtain ⟨h1, h2⟩ := key k hk t
  have eL : ∀ a b, L a b = true ↔ ∃ c ∈ [(0 : Fin 13), 1, 3, 9], a = b + c :=
    fun a b => decide_eq_true_iff
  have eY : ∀ a, Y k t a = true ↔ ∀ p : Fin 13, k.testBit (p - t).val = true →
      ¬ ∃ c ∈ [(0 : Fin 13), 1, 3, 9], p = a + c := fun a =>
    decide_eq_true_iff.trans (forall_congr' fun p => imp_congr_right fun _ => by
      rw [← eL, Bool.not_eq_true])
  refine ⟨fun p hp => ?_, h2.imp (fun h => ?_) (fun h => ?_)⟩
  · obtain ⟨l, hl, hpl⟩ := of_decide_eq_true h1 p (Bool.not_eq_true _ ▸ hp)
    exact ⟨l, (eY l).1 hl, (eL p l).1 hpl⟩
  · obtain ⟨l, hl⟩ := of_decide_eq_true h
    exact ⟨l, fun p hp => (eL p l).1 (hl p hp)⟩
  · obtain ⟨p, hp⟩ := of_decide_eq_true h
    exact ⟨p, fun l hl => (eL p l).1 (hp l ((eY l).2 hl))⟩
