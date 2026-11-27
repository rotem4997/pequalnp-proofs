import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6798

def F (x1 : ℕ) (x2 : Fin (13 : ℕ)) (x3 : ℕ) (x4 : Bool) (x5 : Fin (26 : ℕ)) : Bool :=
  x1.testBit (((if x4 = Bool.true then (13 : ℕ) - x3 else x3) * ↑x5 + ↑x2) % (13 : ℕ) + (13 : ℕ) * if x4 = Bool.true then (1 : ℕ) - ↑x5 / (13 : ℕ) else ↑x5 / (13 : ℕ))

def R (p q : Fin 13) : Bool := decide (p = q ∨ p = q + 1 ∨ p = q + 3 ∨ p = q + 9)

def chk1 (n : ℕ) (a : Fin 13) (m : ℕ) (s : Bool) : Bool :=
  (List.finRange 13).all (fun p => (List.finRange 13).all (fun q => !(F n a m s (Fin.castAdd 13 p) && F n a m s (Fin.natAdd 13 q) && R p q)))
  && (List.finRange 13).all (fun q => decide (((List.finRange 13).filter (fun p => F n a m s (Fin.castAdd 13 p) && R p q)).length ≤ 2))
  && (List.finRange 13).all (fun p => decide (((List.finRange 13).filter (fun q => F n a m s (Fin.natAdd 13 q) && R p q)).length ≤ 2))

def chkAll : Bool :=
  [(7405575 : ℕ), 23330829, 5799955, 22282261, 21757977, 21233693, 19415081, 5275731].all (fun n =>
    (List.finRange 13).all (fun a => [(1 : ℕ), 3, 9].all (fun m => [false, true].all (fun s => chk1 n a m s))))

set_option maxRecDepth 100000 in
theorem chkAll_true : chkAll = true := by decide +kernel

theorem all : ∀ n ∈ [(7405575 : ℕ), 23330829, 5799955, 22282261, 21757977, 21233693, 19415081, 5275731],
    ∀ a : Fin 13, ∀ m ∈ [(1 : ℕ), 3, 9], ∀ s : Bool, chk1 n a m s = true := by
  intro n hn a m hm s
  have h := chkAll_true
  unfold chkAll at h
  rw [List.all_eq_true] at h
  have h1 := h n hn
  rw [List.all_eq_true] at h1
  have h2 := h1 a (List.mem_finRange a)
  rw [List.all_eq_true] at h2
  have h3 := h2 m hm
  rw [List.all_eq_true] at h3
  exact h3 s (by cases s <;> simp)

theorem cardlem (p : Fin 13 → Bool) :
    (Finset.univ.filter (fun i => p i = true)).card = ((List.finRange 13).filter p).length := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter p)]
  congr 1
  ext i
  simp

theorem core (n : ℕ) (a : Fin 13) (m : ℕ) (s : Bool) (h : chk1 n a m s = true) :
    have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | F n a m s (Fin.castAdd (13 : ℕ) x8) = Bool.true};         have x9 : Finset (Fin (13 : ℕ)) := {x9 : Fin (13 : ℕ) | F n a m s (Fin.natAdd (13 : ℕ) x9) = Bool.true};         let x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 x11 : Fin (13 : ℕ)) => x10 = x11 ∨ x10 = x11 + (1 : Fin (13 : ℕ)) ∨ x10 = x11 + (3 : Fin (13 : ℕ)) ∨ x10 = x11 + (9 : Fin (13 : ℕ));         (∀ x11 ∈ x8, ∀ x13 ∈ x9, ¬x10 x11 x13) ∧ (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x10 x12 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x9 | x10 x11 x12}.card ≤ (2 : ℕ) := by
  unfold chk1 at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  try dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq hr
    have hr' : p = q ∨ p = q + 1 ∨ p = q + 3 ∨ p = q + 9 := hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have := h1 p (List.mem_finRange p) q (List.mem_finRange q)
    rw [hp, hq] at this
    simp [R, hr'] at this
  · intro q
    have h := h2 q (List.mem_finRange q)
    rw [← cardlem] at h
    convert h using 2
    ext i
    simp [R]
  · intro p
    have h := h3 p (List.mem_finRange p)
    rw [← cardlem] at h
    convert h using 2
    ext i
    simp [R]

theorem helper : ∀ x2 ∈ [(7405575 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (21233693 : ℕ), (19415081 : ℕ), (5275731 : ℕ)],   ∀ (x4 : Fin (13 : ℕ)),     ∀ x5 ∈ [(1 : ℕ), (3 : ℕ), (9 : ℕ)],       ∀ (x7 : Bool),         have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | F x2 x4 x5 x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true};         have x9 : Finset (Fin (13 : ℕ)) := {x9 : Fin (13 : ℕ) | F x2 x4 x5 x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true};         let x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 x11 : Fin (13 : ℕ)) => x10 = x11 ∨ x10 = x11 + (1 : Fin (13 : ℕ)) ∨ x10 = x11 + (3 : Fin (13 : ℕ)) ∨ x10 = x11 + (9 : Fin (13 : ℕ));         (∀ x11 ∈ x8, ∀ x13 ∈ x9, ¬x10 x11 x13) ∧ (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x10 x12 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x9 | x10 x11 x12}.card ≤ (2 : ℕ) := by
  intro x2 hx2 x4 x5 hx5 x7
  exact core x2 x4 x5 x7 (all x2 hx2 x4 x5 hx5 x7)

end PEqualNP.Outside.L_meta_6798

theorem PEqualNP.Outside.L_meta_6798 : have x1 : ℕ → Fin (13 : ℕ) → ℕ → Bool → Fin (26 : ℕ) → Bool := fun (x1 : ℕ) (x2 : Fin (13 : ℕ)) (x3 : ℕ) (x4 : Bool) (x5 : Fin (26 : ℕ)) => x1.testBit (((if x4 = Bool.true then (13 : ℕ) - x3 else x3) * ↑x5 + ↑x2) % (13 : ℕ) + (13 : ℕ) * if x4 = Bool.true then (1 : ℕ) - ↑x5 / (13 : ℕ) else ↑x5 / (13 : ℕ)); ∀ x2 ∈ [(7405575 : ℕ), (23330829 : ℕ), (5799955 : ℕ), (22282261 : ℕ), (21757977 : ℕ), (21233693 : ℕ), (19415081 : ℕ), (5275731 : ℕ)],   ∀ (x4 : Fin (13 : ℕ)),     ∀ x5 ∈ [(1 : ℕ), (3 : ℕ), (9 : ℕ)],       ∀ (x7 : Bool),         have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | x1 x2 x4 x5 x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true};         have x9 : Finset (Fin (13 : ℕ)) := {x9 : Fin (13 : ℕ) | x1 x2 x4 x5 x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true};         let x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x10 x11 : Fin (13 : ℕ)) => x10 = x11 ∨ x10 = x11 + (1 : Fin (13 : ℕ)) ∨ x10 = x11 + (3 : Fin (13 : ℕ)) ∨ x10 = x11 + (9 : Fin (13 : ℕ));         (∀ x11 ∈ x8, ∀ x13 ∈ x9, ¬x10 x11 x13) ∧ (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x10 x12 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x9 | x10 x11 x12}.card ≤ (2 : ℕ) :=
  PEqualNP.Outside.L_meta_6798.helper
