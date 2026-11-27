import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7099

def mkPerm (f g : List (Fin 21)) (h1 : ∀ x : Fin 21, g.getD (f.getD x 0) 0 = x)
    (h2 : ∀ x : Fin 21, f.getD (g.getD x 0) 0 = x) : Equiv.Perm (Fin 21) :=
  ⟨fun x => f.getD x 0, fun x => g.getD x 0, h1, h2⟩

def P (x5 : ℕ) (x7 : Fin (21 : ℕ)) : Prop :=
  let x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : Finset (Fin (21 : ℕ)) → Finset (Fin (21 : ℕ)) := fun (x2 : Finset (Fin (21 : ℕ))) => {x3 : Fin (21 : ℕ) | ∀ (x4 : Fin (21 : ℕ)), (∀ x5 ∈ x2, ¬x1 x5 x4) → ¬x1 x3 x4}; have x3 : ℕ → Finset (Fin (21 : ℕ)) := fun (x3 : ℕ) => {x4 : Fin (21 : ℕ) | x3.testBit ↑x4 = Bool.true}; have x4 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (19 : ℕ), (7 : ℕ), (389 : ℕ), (23 : ℕ), (15 : ℕ), (31 : ℕ), (95 : ℕ), (1369 : ℕ), (1371 : ℕ), (6799 : ℕ), (5501 : ℕ), (54781 : ℕ), (503803 : ℕ), (2097151 : ℕ)]; ∃ x8 ∈ x4, ∃ (x9 : Equiv.Perm (Fin (21 : ℕ))) (x10 : Equiv.Perm (Fin (21 : ℕ))), (∀ (x11 x12 : Fin (21 : ℕ)), x1 (x9 x11) (x10 x12) ↔ x1 x11 x12) ∧ x2 (Insert.insert x7 (x3 x5)) = Finset.map (Equiv.toEmbedding x9) (x3 x8)

def q0 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] (by decide) (by decide)

theorem c_0_0 : P 0 (0 : Fin 21) :=
  ⟨1, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q1 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 0, 2, 3, 4, 11, 18, 17, 15, 13, 10, 5, 20, 9, 14, 8, 16, 7, 6, 19, 12]
    [1, 0, 2, 3, 4, 11, 18, 17, 15, 13, 10, 5, 20, 9, 14, 8, 16, 7, 6, 19, 12] (by decide) (by decide)

def q2 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 2, 3, 11, 18, 17, 1, 20, 9, 10, 4, 16, 14, 13, 15, 12, 6, 5, 19, 8]
    [0, 7, 2, 3, 11, 18, 17, 1, 20, 9, 10, 4, 16, 14, 13, 15, 12, 6, 5, 19, 8] (by decide) (by decide)

theorem c_0_1 : P 0 (1 : Fin 21) :=
  ⟨1, by decide, q1, q2, by decide +kernel, by decide +kernel⟩

def q3 : Equiv.Perm (Fin 21) :=
  mkPerm [2, 0, 1, 3, 7, 14, 12, 17, 15, 20, 10, 5, 13, 6, 11, 16, 8, 4, 9, 19, 18]
    [1, 2, 0, 3, 17, 11, 13, 4, 16, 18, 10, 14, 6, 12, 5, 8, 15, 7, 20, 19, 9] (by decide) (by decide)

def q4 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 0, 8, 3, 14, 19, 17, 1, 20, 6, 10, 12, 13, 11, 16, 15, 4, 9, 5, 18, 2]
    [1, 7, 20, 3, 16, 18, 9, 0, 2, 17, 10, 13, 11, 12, 4, 15, 14, 6, 19, 5, 8] (by decide) (by decide)

theorem c_0_2 : P 0 (2 : Fin 21) :=
  ⟨1, by decide, q3, q4, by decide +kernel, by decide +kernel⟩

def q5 : Equiv.Perm (Fin 21) :=
  mkPerm [3, 0, 1, 2, 13, 14, 5, 9, 8, 11, 19, 12, 7, 18, 20, 16, 15, 4, 17, 10, 6]
    [1, 2, 3, 0, 17, 6, 20, 12, 8, 7, 19, 9, 11, 4, 5, 16, 15, 18, 13, 10, 14] (by decide) (by decide)

def q6 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 0, 1, 9, 13, 10, 5, 8, 7, 18, 19, 12, 14, 4, 16, 15, 11, 3, 17, 6, 2]
    [1, 2, 20, 17, 13, 6, 19, 8, 7, 3, 5, 16, 11, 4, 12, 15, 14, 18, 9, 10, 0] (by decide) (by decide)

theorem c_0_3 : P 0 (3 : Fin 21) :=
  ⟨1, by decide, q5, q6, by decide +kernel, by decide +kernel⟩

def q7 : Equiv.Perm (Fin 21) :=
  mkPerm [4, 0, 2, 3, 1, 11, 6, 9, 13, 15, 5, 10, 20, 17, 14, 7, 16, 8, 18, 12, 19]
    [1, 4, 2, 3, 0, 10, 6, 15, 17, 7, 11, 5, 19, 8, 14, 9, 16, 13, 18, 20, 12] (by decide) (by decide)

def q8 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 2, 8, 18, 11, 5, 9, 20, 1, 10, 6, 16, 13, 14, 12, 15, 4, 17, 19, 3]
    [0, 9, 2, 20, 17, 6, 11, 1, 3, 7, 10, 5, 15, 13, 14, 16, 12, 18, 4, 19, 8] (by decide) (by decide)

theorem c_0_4 : P 0 (4 : Fin 21) :=
  ⟨1, by decide, q7, q8, by decide +kernel, by decide +kernel⟩

def q9 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 0, 1, 3, 6, 4, 8, 2, 15, 20, 7, 17, 13, 10, 19, 14, 9, 16, 12, 18, 11]
    [1, 2, 7, 3, 5, 0, 4, 10, 6, 16, 13, 20, 18, 12, 15, 8, 17, 11, 19, 14, 9] (by decide) (by decide)

def q10 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 0, 8, 2, 11, 4, 7, 1, 20, 6, 3, 13, 9, 15, 19, 14, 16, 12, 17, 18, 10]
    [1, 7, 3, 10, 5, 0, 9, 6, 2, 12, 20, 4, 17, 11, 15, 13, 16, 18, 19, 14, 8] (by decide) (by decide)

theorem c_0_5 : P 0 (5 : Fin 21) :=
  ⟨1, by decide, q9, q10, by decide +kernel, by decide +kernel⟩

def q11 : Equiv.Perm (Fin 21) :=
  mkPerm [6, 0, 1, 2, 9, 14, 17, 10, 7, 8, 12, 20, 11, 3, 19, 16, 5, 4, 15, 13, 18]
    [1, 2, 3, 13, 17, 16, 0, 8, 9, 4, 7, 12, 10, 19, 5, 18, 15, 6, 20, 14, 11] (by decide) (by decide)

def q12 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 0, 1, 9, 14, 13, 17, 6, 7, 8, 19, 16, 10, 3, 15, 12, 4, 11, 20, 18, 2]
    [1, 2, 20, 13, 16, 0, 7, 8, 9, 3, 12, 17, 15, 5, 4, 14, 11, 6, 19, 10, 18] (by decide) (by decide)

theorem c_0_6 : P 0 (6 : Fin 21) :=
  ⟨1, by decide, q11, q12, by decide +kernel, by decide +kernel⟩

def q13 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 0, 1, 3, 2, 14, 9, 6, 20, 15, 5, 10, 13, 17, 11, 4, 8, 16, 12, 18, 19]
    [1, 2, 4, 3, 15, 10, 7, 0, 16, 6, 11, 14, 18, 12, 5, 9, 17, 13, 19, 20, 8] (by decide) (by decide)

def q14 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 0, 8, 2, 19, 14, 5, 6, 20, 1, 10, 9, 13, 16, 11, 4, 15, 12, 17, 18, 3]
    [1, 9, 3, 20, 15, 6, 7, 0, 2, 11, 10, 14, 17, 12, 5, 16, 13, 18, 19, 4, 8] (by decide) (by decide)

theorem c_0_7 : P 0 (7 : Fin 21) :=
  ⟨1, by decide, q13, q14, by decide +kernel, by decide +kernel⟩

def q15 : Equiv.Perm (Fin 21) :=
  mkPerm [8, 0, 1, 5, 7, 14, 17, 12, 9, 6, 10, 3, 19, 20, 11, 4, 2, 16, 15, 13, 18]
    [1, 2, 16, 11, 15, 3, 9, 4, 0, 8, 10, 14, 7, 19, 5, 18, 17, 6, 20, 12, 13] (by decide) (by decide)

def q16 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 0, 1, 12, 14, 13, 17, 8, 5, 6, 10, 3, 19, 16, 11, 9, 2, 15, 20, 18, 4]
    [1, 2, 16, 11, 20, 8, 9, 0, 7, 15, 10, 14, 3, 5, 4, 17, 13, 6, 19, 12, 18] (by decide) (by decide)

theorem c_0_8 : P 0 (8 : Fin 21) :=
  ⟨1, by decide, q15, q16, by decide +kernel, by decide +kernel⟩

def q17 : Equiv.Perm (Fin 21) :=
  mkPerm [9, 0, 1, 2, 6, 14, 15, 3, 8, 7, 20, 12, 11, 10, 19, 4, 5, 16, 17, 18, 13]
    [1, 2, 3, 7, 15, 16, 4, 9, 8, 0, 13, 12, 11, 20, 5, 6, 17, 18, 19, 14, 10] (by decide) (by decide)

def q18 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 0, 1, 2, 13, 14, 20, 8, 7, 6, 19, 11, 10, 15, 3, 4, 12, 16, 17, 18, 9]
    [1, 2, 3, 14, 15, 0, 9, 8, 7, 20, 12, 11, 16, 4, 5, 13, 17, 18, 19, 10, 6] (by decide) (by decide)

theorem c_0_9 : P 0 (9 : Fin 21) :=
  ⟨1, by decide, q17, q18, by decide +kernel, by decide +kernel⟩

def q19 : Equiv.Perm (Fin 21) :=
  mkPerm [10, 0, 1, 2, 12, 16, 15, 20, 7, 8, 3, 6, 11, 9, 18, 4, 17, 14, 5, 19, 13]
    [1, 2, 3, 10, 15, 18, 11, 8, 9, 13, 0, 12, 4, 20, 17, 6, 5, 16, 14, 19, 7] (by decide) (by decide)

def q20 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 0, 1, 19, 12, 15, 20, 6, 7, 8, 2, 11, 16, 14, 4, 3, 13, 10, 5, 18, 9]
    [1, 2, 10, 15, 14, 18, 7, 8, 9, 20, 17, 11, 4, 16, 13, 5, 12, 0, 19, 3, 6] (by decide) (by decide)

theorem c_0_10 : P 0 (10 : Fin 21) :=
  ⟨1, by decide, q19, q20, by decide +kernel, by decide +kernel⟩

def q21 : Equiv.Perm (Fin 21) :=
  mkPerm [11, 0, 1, 3, 2, 4, 12, 18, 13, 15, 17, 19, 20, 5, 7, 14, 8, 16, 9, 6, 10]
    [1, 2, 4, 3, 5, 13, 19, 14, 16, 18, 20, 0, 6, 8, 15, 9, 17, 10, 7, 11, 12] (by decide) (by decide)

def q22 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 0, 8, 2, 9, 11, 17, 18, 20, 1, 3, 19, 4, 12, 14, 13, 15, 16, 5, 6, 10]
    [1, 9, 3, 10, 12, 18, 19, 0, 2, 4, 20, 5, 13, 15, 14, 16, 17, 6, 7, 11, 8] (by decide) (by decide)

theorem c_0_11 : P 0 (11 : Fin 21) :=
  ⟨1, by decide, q21, q22, by decide +kernel, by decide +kernel⟩

def q23 : Equiv.Perm (Fin 21) :=
  mkPerm [12, 0, 1, 2, 10, 16, 5, 9, 8, 7, 6, 3, 11, 20, 18, 14, 17, 4, 15, 13, 19]
    [1, 2, 3, 11, 17, 6, 10, 9, 8, 7, 4, 12, 0, 19, 15, 18, 5, 16, 14, 20, 13] (by decide) (by decide)

def q24 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 0, 1, 9, 15, 12, 5, 8, 7, 6, 2, 10, 16, 4, 14, 13, 3, 11, 20, 18, 19]
    [1, 2, 10, 16, 13, 6, 9, 8, 7, 3, 11, 17, 5, 15, 14, 4, 12, 0, 19, 20, 18] (by decide) (by decide)

theorem c_0_12 : P 0 (12 : Fin 21) :=
  ⟨1, by decide, q23, q24, by decide +kernel, by decide +kernel⟩

def q25 : Equiv.Perm (Fin 21) :=
  mkPerm [13, 0, 1, 2, 3, 14, 17, 18, 11, 8, 12, 19, 7, 9, 20, 4, 15, 16, 5, 6, 10]
    [1, 2, 3, 4, 15, 18, 19, 12, 9, 13, 20, 8, 10, 0, 5, 16, 17, 6, 7, 11, 14] (by decide) (by decide)

def q26 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 0, 1, 2, 10, 13, 17, 18, 7, 8, 19, 3, 14, 16, 4, 11, 15, 12, 5, 6, 9]
    [1, 2, 3, 11, 14, 18, 19, 8, 9, 20, 4, 15, 17, 5, 12, 16, 13, 6, 7, 10, 0] (by decide) (by decide)

theorem c_0_13 : P 0 (13 : Fin 21) :=
  ⟨1, by decide, q25, q26, by decide +kernel, by decide +kernel⟩

def q27 : Equiv.Perm (Fin 21) :=
  mkPerm [14, 0, 2, 3, 1, 7, 18, 12, 20, 15, 17, 19, 13, 5, 4, 11, 16, 8, 6, 9, 10]
    [1, 4, 2, 3, 14, 13, 18, 5, 17, 19, 20, 15, 7, 12, 0, 9, 16, 10, 6, 11, 8] (by decide) (by decide)

def q28 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 2, 8, 6, 14, 17, 19, 20, 1, 3, 18, 12, 4, 11, 16, 15, 13, 5, 9, 10]
    [0, 9, 2, 10, 13, 18, 4, 1, 3, 19, 20, 14, 12, 17, 5, 16, 15, 6, 11, 7, 8] (by decide) (by decide)

theorem c_0_14 : P 0 (14 : Fin 21) :=
  ⟨1, by decide, q27, q28, by decide +kernel, by decide +kernel⟩

def q29 : Equiv.Perm (Fin 21) :=
  mkPerm [15, 0, 1, 6, 3, 14, 7, 2, 5, 9, 8, 17, 19, 12, 13, 4, 20, 16, 10, 18, 11]
    [1, 2, 7, 4, 15, 8, 3, 6, 10, 9, 18, 20, 13, 14, 5, 0, 17, 11, 19, 12, 16] (by decide) (by decide)

def q30 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 0, 6, 2, 10, 14, 7, 1, 5, 8, 13, 3, 19, 12, 9, 4, 16, 15, 17, 18, 11]
    [1, 7, 3, 11, 15, 8, 2, 6, 9, 14, 4, 20, 13, 10, 5, 17, 16, 18, 19, 12, 0] (by decide) (by decide)

theorem c_0_15 : P 0 (15 : Fin 21) :=
  ⟨1, by decide, q29, q30, by decide +kernel, by decide +kernel⟩

def q31 : Equiv.Perm (Fin 21) :=
  mkPerm [16, 0, 2, 5, 4, 11, 17, 18, 6, 9, 10, 3, 19, 13, 14, 7, 1, 8, 15, 20, 12]
    [1, 16, 2, 11, 4, 3, 8, 15, 17, 9, 10, 5, 20, 13, 14, 18, 0, 6, 7, 12, 19] (by decide) (by decide)

def q32 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 1, 4, 11, 16, 17, 2, 5, 9, 10, 3, 18, 13, 14, 6, 8, 15, 20, 19, 12]
    [0, 2, 7, 11, 3, 8, 15, 1, 16, 9, 10, 4, 20, 13, 14, 17, 5, 6, 12, 19, 18] (by decide) (by decide)

theorem c_0_16 : P 0 (16 : Fin 21) :=
  ⟨1, by decide, q31, q32, by decide +kernel, by decide +kernel⟩

def q33 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 0, 1, 3, 10, 16, 9, 5, 15, 20, 6, 2, 13, 7, 18, 4, 12, 14, 8, 11, 19]
    [1, 2, 11, 3, 15, 7, 10, 13, 18, 6, 4, 19, 16, 12, 17, 8, 5, 0, 14, 20, 9] (by decide) (by decide)

def q34 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 0, 8, 10, 15, 16, 5, 1, 20, 6, 2, 9, 12, 14, 4, 11, 19, 13, 7, 18, 3]
    [1, 7, 10, 20, 14, 6, 9, 18, 2, 11, 3, 15, 12, 17, 13, 4, 5, 0, 19, 16, 8] (by decide) (by decide)

theorem c_0_17 : P 0 (17 : Fin 21) :=
  ⟨1, by decide, q33, q34, by decide +kernel, by decide +kernel⟩

def q35 : Equiv.Perm (Fin 21) :=
  mkPerm [18, 0, 1, 2, 10, 14, 15, 13, 11, 7, 20, 19, 8, 6, 12, 16, 17, 4, 5, 9, 3]
    [1, 2, 3, 20, 17, 18, 13, 9, 12, 19, 4, 8, 14, 7, 5, 6, 15, 16, 0, 11, 10] (by decide) (by decide)

def q36 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 0, 1, 9, 10, 14, 20, 18, 7, 6, 19, 15, 13, 11, 12, 16, 3, 4, 5, 8, 2]
    [1, 2, 20, 16, 17, 18, 9, 8, 19, 3, 4, 13, 14, 12, 5, 11, 15, 0, 7, 10, 6] (by decide) (by decide)

theorem c_0_18 : P 0 (18 : Fin 21) :=
  ⟨1, by decide, q35, q36, by decide +kernel, by decide +kernel⟩

def q37 : Equiv.Perm (Fin 21) :=
  mkPerm [19, 0, 1, 2, 6, 4, 17, 18, 11, 7, 10, 13, 8, 20, 9, 14, 5, 16, 15, 3, 12]
    [1, 2, 3, 19, 5, 16, 4, 9, 12, 14, 10, 8, 20, 11, 15, 18, 17, 6, 7, 0, 13] (by decide) (by decide)

def q38 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 0, 1, 2, 11, 3, 17, 18, 7, 6, 9, 13, 4, 16, 14, 10, 12, 15, 20, 8, 19]
    [1, 2, 3, 5, 12, 0, 9, 8, 19, 10, 15, 4, 16, 11, 14, 17, 13, 6, 7, 20, 18] (by decide) (by decide)

theorem c_0_19 : P 0 (19 : Fin 21) :=
  ⟨1, by decide, q37, q38, by decide +kernel, by decide +kernel⟩

def q39 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 0] (by decide) (by decide)

theorem c_0_20 : P 0 (20 : Fin 21) :=
  ⟨1, by decide, q39, q39, by decide +kernel, by decide +kernel⟩

theorem c_1_0 : P 1 (0 : Fin 21) :=
  ⟨1, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_1_1 : P 1 (1 : Fin 21) :=
  ⟨3, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q40 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 1, 3, 7, 5, 9, 4, 16, 6, 10, 14, 18, 20, 11, 15, 8, 17, 12, 19, 13]
    [0, 2, 1, 3, 7, 5, 9, 4, 16, 6, 10, 14, 18, 20, 11, 15, 8, 17, 12, 19, 13] (by decide) (by decide)

def q41 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 1, 8, 3, 12, 5, 9, 0, 2, 6, 10, 14, 4, 16, 11, 15, 13, 17, 19, 18, 20]
    [7, 1, 8, 3, 12, 5, 9, 0, 2, 6, 10, 14, 4, 16, 11, 15, 13, 17, 19, 18, 20] (by decide) (by decide)

theorem c_1_2 : P 1 (2 : Fin 21) :=
  ⟨3, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

def q42 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 3, 1, 2, 13, 12, 17, 4, 16, 18, 19, 14, 6, 11, 20, 8, 15, 9, 5, 10, 7]
    [0, 2, 3, 1, 7, 18, 12, 20, 15, 17, 19, 13, 5, 4, 11, 16, 8, 6, 9, 10, 14] (by decide) (by decide)

def q43 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 8, 1, 9, 12, 17, 3, 0, 2, 18, 19, 13, 11, 16, 4, 15, 14, 5, 10, 6, 7]
    [7, 2, 8, 6, 14, 17, 19, 20, 1, 3, 18, 12, 4, 11, 16, 15, 13, 5, 9, 10, 0] (by decide) (by decide)

theorem c_1_3 : P 1 (3 : Fin 21) :=
  ⟨3, by decide, q42, q43, by decide +kernel, by decide +kernel⟩

def q44 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 4, 2, 3, 1, 10, 18, 8, 7, 17, 5, 11, 19, 15, 14, 13, 16, 9, 6, 12, 20]
    [0, 4, 2, 3, 1, 10, 18, 8, 7, 17, 5, 11, 19, 15, 14, 13, 16, 9, 6, 12, 20] (by decide) (by decide)

def q45 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 9, 2, 8, 6, 17, 4, 7, 3, 1, 10, 18, 15, 14, 13, 12, 16, 5, 11, 19, 20]
    [0, 9, 2, 8, 6, 17, 4, 7, 3, 1, 10, 18, 15, 14, 13, 12, 16, 5, 11, 19, 20] (by decide) (by decide)

theorem c_1_4 : P 1 (4 : Fin 21) :=
  ⟨3, by decide, q44, q45, by decide +kernel, by decide +kernel⟩

def q46 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 5, 1, 3, 6, 17, 12, 16, 14, 10, 7, 4, 11, 20, 19, 15, 9, 2, 8, 18, 13]
    [0, 2, 17, 3, 11, 1, 4, 10, 18, 16, 9, 12, 6, 20, 8, 15, 7, 5, 19, 14, 13] (by decide) (by decide)

def q47 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 1, 8, 2, 13, 17, 12, 0, 10, 6, 3, 11, 16, 19, 15, 14, 9, 7, 4, 18, 20]
    [7, 1, 3, 10, 18, 0, 9, 17, 2, 16, 8, 11, 6, 4, 15, 14, 12, 5, 19, 13, 20] (by decide) (by decide)

theorem c_1_5 : P 1 (5 : Fin 21) :=
  ⟨3, by decide, q46, q47, by decide +kernel, by decide +kernel⟩

def q48 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 1, 2, 9, 20, 15, 4, 16, 3, 12, 14, 18, 8, 19, 7, 5, 10, 17, 13, 11]
    [0, 2, 3, 9, 7, 16, 1, 15, 13, 4, 17, 20, 10, 19, 11, 6, 8, 18, 12, 14, 5] (by decide) (by decide)

def q49 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 6, 1, 9, 16, 20, 11, 0, 2, 8, 19, 14, 4, 15, 3, 12, 10, 17, 13, 18, 7]
    [7, 2, 8, 14, 12, 0, 1, 20, 9, 3, 16, 6, 15, 18, 11, 13, 4, 17, 19, 10, 5] (by decide) (by decide)

theorem c_1_6 : P 1 (6 : Fin 21) :=
  ⟨3, by decide, q48, q49, by decide +kernel, by decide +kernel⟩

def q50 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 1, 3, 2, 10, 12, 16, 4, 17, 5, 14, 19, 15, 11, 20, 8, 6, 9, 18, 13]
    [0, 2, 4, 3, 8, 10, 17, 1, 16, 18, 5, 14, 6, 20, 11, 13, 7, 9, 19, 12, 15] (by decide) (by decide)

def q51 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 6, 8, 2, 9, 17, 12, 0, 3, 1, 10, 19, 15, 11, 16, 4, 13, 5, 14, 18, 20]
    [7, 9, 3, 8, 15, 17, 1, 0, 2, 4, 10, 13, 6, 16, 18, 12, 14, 5, 19, 11, 20] (by decide) (by decide)

theorem c_1_7 : P 1 (7 : Fin 21) :=
  ⟨3, by decide, q50, q51, by decide +kernel, by decide +kernel⟩

def q52 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 1, 5, 7, 3, 15, 16, 4, 20, 10, 14, 18, 6, 11, 9, 2, 12, 17, 13, 19]
    [0, 2, 16, 5, 8, 3, 13, 4, 1, 15, 10, 14, 17, 19, 11, 6, 7, 18, 12, 20, 9] (by decide) (by decide)

def q53 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 8, 1, 12, 3, 20, 15, 0, 4, 6, 10, 14, 2, 11, 16, 9, 19, 17, 13, 18, 5]
    [7, 2, 12, 4, 8, 20, 9, 0, 1, 15, 10, 13, 3, 18, 11, 6, 14, 17, 19, 16, 5] (by decide) (by decide)

theorem c_1_8 : P 1 (8 : Fin 21) :=
  ⟨3, by decide, q52, q53, by decide +kernel, by decide +kernel⟩

def q54 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 9, 1, 2, 6, 12, 17, 16, 4, 10, 20, 14, 13, 7, 19, 8, 5, 3, 15, 18, 11]
    [0, 2, 3, 17, 8, 16, 4, 13, 15, 1, 9, 20, 5, 12, 11, 18, 7, 6, 19, 14, 10] (by decide) (by decide)

def q55 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 8, 1, 2, 11, 17, 16, 0, 9, 6, 19, 13, 12, 3, 15, 4, 10, 20, 14, 18, 7]
    [7, 2, 3, 13, 15, 0, 9, 20, 1, 8, 16, 4, 12, 11, 18, 14, 6, 5, 19, 10, 17] (by decide) (by decide)

theorem c_1_9 : P 1 (9 : Fin 21) :=
  ⟨3, by decide, q54, q55, by decide +kernel, by decide +kernel⟩

def q56 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 10, 1, 2, 12, 6, 5, 14, 4, 9, 3, 16, 13, 8, 18, 7, 17, 20, 15, 19, 11]
    [0, 2, 3, 10, 8, 6, 5, 15, 13, 9, 1, 20, 4, 12, 7, 18, 11, 16, 14, 19, 17] (by decide) (by decide)

def q57 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 6, 1, 19, 11, 5, 10, 0, 9, 8, 2, 12, 13, 4, 14, 3, 16, 20, 15, 18, 7]
    [7, 2, 10, 15, 13, 5, 1, 20, 9, 8, 6, 4, 11, 12, 14, 18, 16, 0, 19, 3, 17] (by decide) (by decide)

theorem c_1_10 : P 1 (10 : Fin 21) :=
  ⟨3, by decide, q56, q57, by decide +kernel, by decide +kernel⟩

def q58 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 11, 1, 3, 2, 19, 9, 16, 14, 5, 17, 4, 10, 15, 7, 13, 8, 18, 12, 6, 20]
    [0, 2, 4, 3, 11, 9, 19, 14, 16, 6, 12, 1, 18, 15, 8, 13, 7, 10, 17, 5, 20] (by decide) (by decide)

def q59 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 18, 8, 2, 19, 5, 16, 0, 10, 1, 3, 9, 15, 14, 12, 13, 4, 17, 11, 6, 20]
    [7, 9, 3, 10, 16, 5, 19, 0, 2, 11, 8, 18, 14, 15, 13, 12, 6, 17, 1, 4, 20] (by decide) (by decide)

theorem c_1_11 : P 1 (11 : Fin 21) :=
  ⟨3, by decide, q58, q59, by decide +kernel, by decide +kernel⟩

def q60 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 12, 1, 2, 10, 3, 15, 4, 14, 20, 6, 16, 19, 7, 18, 8, 17, 9, 5, 13, 11]
    [0, 2, 3, 5, 7, 18, 10, 13, 15, 17, 4, 20, 1, 19, 8, 6, 11, 16, 14, 12, 9] (by decide) (by decide)

def q61 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 8, 1, 9, 10, 20, 11, 0, 19, 6, 2, 15, 3, 14, 4, 13, 16, 5, 12, 18, 7]
    [7, 2, 10, 12, 14, 17, 9, 20, 1, 3, 4, 6, 18, 15, 13, 11, 16, 0, 19, 8, 5] (by decide) (by decide)

theorem c_1_12 : P 1 (12 : Fin 21) :=
  ⟨3, by decide, q60, q61, by decide +kernel, by decide +kernel⟩

def q62 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 13, 1, 2, 3, 19, 5, 16, 4, 9, 12, 14, 10, 8, 20, 11, 15, 18, 17, 6, 7]
    [0, 2, 3, 4, 8, 6, 19, 20, 13, 9, 12, 15, 10, 1, 11, 16, 7, 18, 17, 5, 14] (by decide) (by decide)

def q63 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 18, 1, 2, 3, 5, 12, 0, 9, 8, 19, 10, 15, 4, 16, 11, 14, 17, 13, 6, 7]
    [7, 2, 3, 4, 13, 5, 19, 20, 9, 8, 11, 15, 6, 18, 16, 12, 14, 17, 1, 10, 0] (by decide) (by decide)

theorem c_1_13 : P 1 (13 : Fin 21) :=
  ⟨3, by decide, q62, q63, by decide +kernel, by decide +kernel⟩

def q64 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 14, 2, 3, 1, 19, 6, 8, 11, 5, 17, 7, 10, 15, 4, 20, 16, 12, 18, 9, 13]
    [0, 4, 2, 3, 14, 9, 6, 11, 7, 19, 12, 8, 17, 20, 1, 13, 16, 10, 18, 5, 15] (by decide) (by decide)

def q65 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 2, 8, 18, 5, 13, 7, 10, 1, 3, 6, 15, 11, 4, 16, 12, 17, 14, 9, 20]
    [0, 9, 2, 10, 14, 5, 11, 7, 3, 19, 8, 13, 16, 6, 18, 12, 15, 17, 4, 1, 20] (by decide) (by decide)

theorem c_1_14 : P 1 (14 : Fin 21) :=
  ⟨3, by decide, q64, q65, by decide +kernel, by decide +kernel⟩

def q66 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 15, 1, 6, 3, 17, 10, 16, 4, 12, 8, 14, 11, 9, 13, 5, 20, 2, 7, 18, 19]
    [0, 2, 17, 4, 8, 15, 3, 18, 10, 13, 6, 12, 9, 14, 11, 1, 7, 5, 19, 20, 16] (by decide) (by decide)

def q67 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 1, 6, 2, 3, 17, 15, 0, 11, 8, 13, 10, 16, 9, 12, 4, 19, 7, 14, 18, 5]
    [7, 1, 3, 4, 15, 20, 2, 17, 9, 13, 11, 8, 14, 10, 18, 6, 12, 5, 19, 16, 0] (by decide) (by decide)

theorem c_1_15 : P 1 (15 : Fin 21) :=
  ⟨3, by decide, q66, q67, by decide +kernel, by decide +kernel⟩

def q68 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 16, 2, 5, 4, 3, 15, 8, 7, 13, 10, 11, 12, 9, 14, 6, 1, 18, 17, 20, 19]
    [0, 16, 2, 5, 4, 3, 15, 8, 7, 13, 10, 11, 12, 9, 14, 6, 1, 18, 17, 20, 19] (by decide) (by decide)

def q69 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 1, 4, 3, 20, 15, 7, 12, 9, 10, 11, 8, 14, 13, 6, 18, 17, 16, 19, 5]
    [0, 2, 1, 4, 3, 20, 15, 7, 12, 9, 10, 11, 8, 14, 13, 6, 18, 17, 16, 19, 5] (by decide) (by decide)

theorem c_1_16 : P 1 (16 : Fin 21) :=
  ⟨3, by decide, q68, q69, by decide +kernel, by decide +kernel⟩

def q70 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 17, 1, 3, 10, 2, 8, 14, 4, 7, 6, 16, 19, 20, 18, 15, 12, 5, 9, 11, 13]
    [0, 2, 5, 3, 8, 17, 10, 9, 6, 18, 4, 19, 16, 20, 7, 15, 11, 1, 14, 12, 13] (by decide) (by decide)

def q71 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 1, 8, 10, 9, 7, 13, 0, 3, 6, 2, 15, 19, 4, 14, 11, 12, 5, 16, 18, 20]
    [7, 1, 10, 8, 13, 17, 9, 5, 2, 4, 3, 15, 16, 6, 14, 11, 18, 0, 19, 12, 20] (by decide) (by decide)

theorem c_1_17 : P 1 (17 : Fin 21) :=
  ⟨3, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

def q72 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 1, 2, 10, 19, 5, 4, 16, 6, 20, 14, 3, 7, 12, 11, 17, 13, 15, 9, 8]
    [0, 2, 3, 12, 7, 6, 9, 13, 20, 19, 4, 15, 14, 17, 11, 18, 8, 16, 1, 5, 10] (by decide) (by decide)

def q73 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 18, 1, 9, 15, 5, 4, 0, 2, 6, 19, 10, 3, 12, 11, 16, 13, 20, 14, 8, 7]
    [7, 2, 8, 12, 6, 5, 9, 20, 19, 3, 11, 14, 13, 16, 18, 4, 15, 0, 1, 10, 17] (by decide) (by decide)

theorem c_1_18 : P 1 (18 : Fin 21) :=
  ⟨3, by decide, q72, q73, by decide +kernel, by decide +kernel⟩

def q74 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 1, 2, 6, 13, 15, 16, 14, 20, 10, 4, 12, 7, 9, 11, 5, 18, 17, 3, 8]
    [0, 2, 3, 19, 11, 16, 4, 13, 20, 14, 10, 15, 12, 5, 8, 6, 7, 18, 17, 1, 9] (by decide) (by decide)

def q75 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 18, 1, 2, 13, 20, 15, 0, 19, 6, 9, 11, 12, 14, 16, 10, 4, 17, 3, 8, 7]
    [7, 2, 3, 18, 16, 0, 9, 20, 19, 10, 15, 11, 12, 4, 13, 6, 14, 17, 1, 8, 5] (by decide) (by decide)

theorem c_1_19 : P 1 (19 : Fin 21) :=
  ⟨3, by decide, q74, q75, by decide +kernel, by decide +kernel⟩

def q76 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 20, 1, 2, 3, 10, 17, 16, 14, 12, 9, 4, 19, 8, 13, 7, 15, 6, 5, 18, 11]
    [0, 2, 3, 4, 11, 18, 17, 15, 13, 10, 5, 20, 9, 14, 8, 16, 7, 6, 19, 12, 1] (by decide) (by decide)

def q77 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 6, 1, 2, 10, 17, 16, 0, 19, 8, 9, 3, 15, 13, 12, 14, 11, 5, 4, 18, 7]
    [7, 2, 3, 11, 18, 17, 1, 20, 9, 10, 4, 16, 14, 13, 15, 12, 6, 5, 19, 8, 0] (by decide) (by decide)

theorem c_1_20 : P 1 (20 : Fin 21) :=
  ⟨3, by decide, q76, q77, by decide +kernel, by decide +kernel⟩

theorem c_2_0 : P 3 (0 : Fin 21) :=
  ⟨3, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_2_1 : P 3 (1 : Fin 21) :=
  ⟨3, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_2_2 : P 3 (2 : Fin 21) :=
  ⟨7, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q78 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 3, 2, 4, 12, 18, 13, 15, 17, 19, 20, 5, 7, 14, 8, 16, 9, 6, 10, 11]
    [0, 1, 3, 2, 4, 12, 18, 13, 15, 17, 19, 20, 5, 7, 14, 8, 16, 9, 6, 10, 11] (by decide) (by decide)

def q79 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 2, 9, 11, 17, 18, 20, 1, 3, 19, 4, 12, 14, 13, 15, 16, 5, 6, 10, 7]
    [0, 8, 2, 9, 11, 17, 18, 20, 1, 3, 19, 4, 12, 14, 13, 15, 16, 5, 6, 10, 7] (by decide) (by decide)

theorem c_2_3 : P 3 (3 : Fin 21) :=
  ⟨7, by decide, q78, q79, by decide +kernel, by decide +kernel⟩

theorem c_2_4 : P 3 (4 : Fin 21) :=
  ⟨19, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q80 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 5, 3, 4, 2, 11, 19, 9, 8, 18, 6, 12, 20, 16, 15, 14, 17, 10, 7, 13]
    [0, 1, 5, 3, 4, 2, 11, 19, 9, 8, 18, 6, 12, 20, 16, 15, 14, 17, 10, 7, 13] (by decide) (by decide)

def q81 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 10, 3, 9, 7, 18, 5, 8, 4, 2, 11, 19, 16, 15, 14, 13, 17, 6, 12, 20]
    [0, 1, 10, 3, 9, 7, 18, 5, 8, 4, 2, 11, 19, 16, 15, 14, 13, 17, 6, 12, 20] (by decide) (by decide)

theorem c_2_5 : P 3 (5 : Fin 21) :=
  ⟨7, by decide, q80, q81, by decide +kernel, by decide +kernel⟩

def q82 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 6, 2, 4, 20, 3, 9, 5, 15, 12, 19, 17, 11, 14, 7, 16, 10, 18, 13, 8]
    [0, 1, 3, 6, 4, 8, 2, 15, 20, 7, 17, 13, 10, 19, 14, 9, 16, 12, 18, 11, 5] (by decide) (by decide)

def q83 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 2, 9, 4, 20, 8, 5, 1, 11, 19, 3, 16, 10, 14, 12, 15, 17, 18, 13, 7]
    [0, 8, 2, 11, 4, 7, 1, 20, 6, 3, 13, 9, 15, 19, 14, 16, 12, 17, 18, 10, 5] (by decide) (by decide)

theorem c_2_6 : P 3 (6 : Fin 21) :=
  ⟨7, by decide, q82, q83, by decide +kernel, by decide +kernel⟩

def q84 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 7, 3, 14, 6, 19, 11, 8, 9, 18, 2, 12, 15, 16, 20, 4, 10, 17, 5, 13]
    [0, 1, 11, 3, 16, 19, 5, 2, 8, 9, 17, 7, 12, 20, 4, 13, 14, 18, 10, 6, 15] (by decide) (by decide)

def q85 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 3, 10, 13, 5, 18, 7, 8, 14, 2, 19, 11, 15, 16, 4, 9, 17, 1, 12, 20]
    [0, 18, 10, 2, 15, 5, 1, 7, 8, 16, 3, 12, 19, 4, 9, 13, 14, 17, 6, 11, 20] (by decide) (by decide)

theorem c_2_7 : P 3 (7 : Fin 21) :=
  ⟨7, by decide, q84, q85, by decide +kernel, by decide +kernel⟩

def q86 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 8, 5, 14, 12, 18, 11, 2, 17, 13, 7, 15, 6, 16, 9, 4, 3, 20, 10, 19]
    [0, 1, 8, 17, 16, 3, 13, 11, 2, 15, 19, 7, 5, 10, 4, 12, 14, 9, 6, 20, 18] (by decide) (by decide)

def q87 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 4, 10, 19, 17, 18, 7, 1, 13, 12, 14, 11, 2, 16, 9, 3, 20, 6, 15, 5]
    [0, 8, 13, 16, 2, 20, 18, 7, 1, 15, 3, 12, 10, 9, 11, 19, 14, 5, 6, 4, 17] (by decide) (by decide)

theorem c_2_8 : P 3 (8 : Fin 21) :=
  ⟨7, by decide, q86, q87, by decide +kernel, by decide +kernel⟩

def q88 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 2, 14, 3, 13, 19, 5, 15, 18, 6, 17, 7, 16, 8, 4, 12, 10, 20, 11]
    [0, 1, 3, 5, 16, 8, 11, 13, 15, 2, 18, 20, 17, 6, 4, 9, 14, 12, 10, 7, 19] (by decide) (by decide)

def q89 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 9, 19, 10, 20, 18, 5, 1, 14, 2, 13, 3, 12, 15, 4, 11, 17, 6, 16, 7]
    [0, 8, 10, 12, 15, 7, 18, 20, 1, 2, 4, 16, 13, 11, 9, 14, 19, 17, 6, 3, 5] (by decide) (by decide)

theorem c_2_9 : P 3 (9 : Fin 21) :=
  ⟨7, by decide, q88, q89, by decide +kernel, by decide +kernel⟩

def q90 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 10, 2, 14, 6, 9, 12, 17, 5, 3, 18, 15, 11, 16, 7, 4, 20, 13, 19, 8]
    [0, 1, 3, 10, 16, 9, 5, 15, 20, 6, 2, 13, 7, 18, 4, 12, 14, 8, 11, 19, 17] (by decide) (by decide)

def q91 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 9, 19, 13, 5, 8, 17, 1, 10, 2, 14, 11, 16, 12, 3, 4, 20, 18, 15, 7]
    [0, 8, 10, 15, 16, 5, 1, 20, 6, 2, 9, 12, 14, 4, 11, 19, 13, 7, 18, 3, 17] (by decide) (by decide)

theorem c_2_10 : P 3 (10 : Fin 21) :=
  ⟨7, by decide, q90, q91, by decide +kernel, by decide +kernel⟩

def q92 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 11, 3, 4, 18, 10, 7, 8, 12, 6, 2, 9, 15, 16, 13, 14, 19, 5, 17, 20]
    [0, 1, 11, 3, 4, 18, 10, 7, 8, 12, 6, 2, 9, 15, 16, 13, 14, 19, 5, 17, 20] (by decide) (by decide)

def q93 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 10, 3, 4, 17, 6, 7, 8, 11, 2, 9, 14, 15, 12, 13, 19, 5, 1, 16, 20]
    [0, 18, 10, 3, 4, 17, 6, 7, 8, 11, 2, 9, 14, 15, 12, 13, 19, 5, 1, 16, 20] (by decide) (by decide)

theorem c_2_11 : P 3 (11 : Fin 21) :=
  ⟨7, by decide, q92, q93, by decide +kernel, by decide +kernel⟩

def q94 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 12, 2, 4, 3, 20, 10, 17, 15, 6, 18, 5, 11, 16, 8, 14, 9, 19, 13, 7]
    [0, 1, 3, 5, 4, 12, 10, 20, 15, 17, 7, 13, 2, 19, 16, 9, 14, 8, 11, 18, 6] (by decide) (by decide)

def q95 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 19, 9, 3, 20, 6, 17, 1, 11, 2, 4, 10, 16, 15, 13, 14, 5, 18, 12, 7]
    [0, 8, 10, 4, 11, 17, 6, 20, 1, 3, 12, 9, 19, 15, 16, 14, 13, 7, 18, 2, 5] (by decide) (by decide)

theorem c_2_12 : P 3 (12 : Fin 21) :=
  ⟨7, by decide, q94, q95, by decide +kernel, by decide +kernel⟩

def q96 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 13, 2, 14, 18, 10, 20, 15, 17, 6, 3, 5, 8, 16, 11, 4, 19, 9, 12, 7]
    [0, 1, 3, 11, 16, 12, 10, 20, 13, 18, 6, 15, 19, 2, 4, 8, 14, 9, 5, 17, 7] (by decide) (by decide)

def q97 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 9, 19, 14, 17, 6, 20, 1, 13, 2, 10, 4, 15, 16, 11, 3, 5, 8, 12, 7]
    [0, 8, 10, 16, 12, 17, 6, 20, 18, 2, 11, 15, 19, 9, 4, 13, 14, 5, 1, 3, 7] (by decide) (by decide)

theorem c_2_13 : P 3 (13 : Fin 21) :=
  ⟨7, by decide, q96, q97, by decide +kernel, by decide +kernel⟩

def q98 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 3, 14, 17, 18, 11, 8, 12, 19, 7, 9, 20, 4, 15, 16, 5, 6, 10, 13]
    [0, 1, 2, 3, 14, 17, 18, 11, 8, 12, 19, 7, 9, 20, 4, 15, 16, 5, 6, 10, 13] (by decide) (by decide)

def q99 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 10, 13, 17, 18, 7, 8, 19, 3, 14, 16, 4, 11, 15, 12, 5, 6, 9, 20]
    [0, 1, 2, 10, 13, 17, 18, 7, 8, 19, 3, 14, 16, 4, 11, 15, 12, 5, 6, 9, 20] (by decide) (by decide)

theorem c_2_14 : P 3 (14 : Fin 21) :=
  ⟨19, by decide, q98, q99, by decide +kernel, by decide +kernel⟩

def q100 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 15, 6, 14, 2, 11, 13, 20, 7, 18, 3, 10, 9, 16, 5, 4, 17, 12, 8, 19]
    [0, 1, 5, 11, 16, 15, 3, 9, 19, 13, 12, 6, 18, 7, 4, 2, 14, 17, 10, 20, 8] (by decide) (by decide)

def q101 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 11, 13, 19, 7, 18, 20, 6, 14, 2, 10, 9, 16, 12, 4, 3, 17, 8, 15, 5]
    [0, 1, 10, 16, 15, 20, 8, 5, 18, 12, 11, 2, 14, 3, 9, 19, 13, 17, 6, 4, 7] (by decide) (by decide)

theorem c_2_15 : P 3 (15 : Fin 21) :=
  ⟨7, by decide, q100, q101, by decide +kernel, by decide +kernel⟩

def q102 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 9, 16, 15, 13, 11, 8, 3, 18, 7, 12, 6, 14, 5, 4, 17, 10, 20, 19]
    [0, 1, 2, 9, 16, 15, 13, 11, 8, 3, 18, 7, 12, 6, 14, 5, 4, 17, 10, 20, 19] (by decide) (by decide)

def q103 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 16, 15, 20, 18, 7, 8, 2, 14, 12, 11, 13, 10, 4, 3, 17, 6, 19, 5]
    [0, 1, 9, 16, 15, 20, 18, 7, 8, 2, 14, 12, 11, 13, 10, 4, 3, 17, 6, 19, 5] (by decide) (by decide)

theorem c_2_16 : P 3 (16 : Fin 21) :=
  ⟨19, by decide, q102, q103, by decide +kernel, by decide +kernel⟩

def q104 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 17, 3, 14, 2, 7, 10, 12, 8, 6, 18, 9, 13, 16, 15, 4, 5, 19, 11, 20]
    [0, 1, 5, 3, 16, 17, 10, 6, 9, 12, 7, 19, 8, 13, 4, 15, 14, 2, 11, 18, 20] (by decide) (by decide)

def q105 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 3, 10, 19, 7, 6, 17, 8, 13, 2, 14, 9, 12, 15, 11, 4, 5, 18, 16, 20]
    [0, 1, 10, 2, 16, 17, 6, 5, 8, 12, 3, 15, 13, 9, 11, 14, 19, 7, 18, 4, 20] (by decide) (by decide)

theorem c_2_17 : P 3 (17 : Fin 21) :=
  ⟨7, by decide, q104, q105, by decide +kernel, by decide +kernel⟩

def q106 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 18, 2, 4, 19, 6, 10, 17, 5, 20, 12, 15, 8, 14, 11, 16, 13, 3, 9, 7]
    [0, 1, 3, 18, 4, 9, 6, 20, 13, 19, 7, 15, 11, 17, 14, 12, 16, 8, 2, 5, 10] (by decide) (by decide)

def q107 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 2, 9, 3, 5, 6, 17, 1, 4, 19, 11, 15, 13, 10, 16, 12, 20, 8, 14, 7]
    [0, 8, 2, 4, 9, 5, 6, 20, 18, 3, 14, 11, 16, 13, 19, 12, 15, 7, 1, 10, 17] (by decide) (by decide)

theorem c_2_18 : P 3 (18 : Fin 21) :=
  ⟨7, by decide, q106, q107, by decide +kernel, by decide +kernel⟩

def q108 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 19, 2, 4, 18, 12, 9, 5, 17, 3, 6, 15, 7, 16, 11, 14, 13, 20, 10, 8]
    [0, 1, 3, 10, 4, 8, 11, 13, 20, 7, 19, 15, 6, 17, 16, 12, 14, 9, 5, 2, 18] (by decide) (by decide)

def q109 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 19, 9, 4, 17, 8, 5, 1, 3, 2, 11, 14, 12, 16, 10, 13, 20, 6, 15, 7]
    [0, 8, 10, 9, 4, 7, 18, 20, 6, 3, 15, 11, 13, 16, 12, 19, 14, 5, 1, 2, 17] (by decide) (by decide)

theorem c_2_19 : P 3 (19 : Fin 21) :=
  ⟨7, by decide, q108, q109, by decide +kernel, by decide +kernel⟩

def q110 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 20, 2, 4, 6, 19, 13, 15, 5, 18, 3, 17, 8, 16, 7, 14, 10, 12, 9, 11]
    [0, 1, 3, 11, 4, 9, 5, 15, 13, 19, 17, 20, 18, 7, 16, 8, 14, 12, 10, 6, 2] (by decide) (by decide)

def q111 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 19, 9, 11, 5, 18, 20, 1, 4, 2, 3, 13, 15, 12, 14, 10, 17, 8, 16, 7]
    [0, 8, 10, 11, 9, 5, 1, 20, 18, 3, 16, 4, 14, 12, 15, 13, 19, 17, 6, 2, 7] (by decide) (by decide)

theorem c_2_20 : P 3 (20 : Fin 21) :=
  ⟨7, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_3_0 : P 19 (0 : Fin 21) :=
  ⟨19, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_3_1 : P 19 (1 : Fin 21) :=
  ⟨19, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_3_2 : P 19 (2 : Fin 21) :=
  ⟨23, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_3_3 : P 19 (3 : Fin 21) :=
  ⟨23, by decide, q78, q79, by decide +kernel, by decide +kernel⟩

theorem c_3_4 : P 19 (4 : Fin 21) :=
  ⟨19, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_3_5 : P 19 (5 : Fin 21) :=
  ⟨23, by decide, q80, q81, by decide +kernel, by decide +kernel⟩

theorem c_3_6 : P 19 (6 : Fin 21) :=
  ⟨23, by decide, q82, q83, by decide +kernel, by decide +kernel⟩

def q112 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 7, 5, 4, 10, 12, 8, 2, 17, 3, 11, 15, 19, 14, 6, 16, 20, 13, 18, 9]
    [0, 1, 8, 10, 4, 3, 15, 2, 7, 20, 5, 11, 6, 18, 14, 12, 16, 9, 19, 13, 17] (by decide) (by decide)

def q113 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 12, 4, 9, 17, 8, 7, 1, 3, 10, 11, 15, 19, 13, 2, 16, 20, 18, 14, 5]
    [0, 8, 15, 9, 3, 20, 1, 7, 6, 4, 10, 11, 2, 14, 19, 12, 16, 5, 18, 13, 17] (by decide) (by decide)

theorem c_3_7 : P 19 (7 : Fin 21) :=
  ⟨23, by decide, q112, q113, by decide +kernel, by decide +kernel⟩

def q114 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 8, 6, 4, 3, 13, 11, 7, 20, 18, 2, 10, 5, 16, 9, 14, 12, 17, 15, 19]
    [0, 1, 11, 5, 4, 13, 3, 8, 2, 15, 12, 7, 17, 6, 16, 19, 14, 18, 10, 20, 9] (by decide) (by decide)

def q115 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 13, 11, 3, 20, 18, 7, 6, 4, 2, 9, 10, 12, 16, 14, 19, 17, 1, 15, 5]
    [0, 18, 10, 4, 9, 20, 8, 7, 1, 11, 12, 3, 13, 2, 15, 19, 14, 17, 6, 16, 5] (by decide) (by decide)

theorem c_3_8 : P 19 (8 : Fin 21) :=
  ⟨23, by decide, q114, q115, by decide +kernel, by decide +kernel⟩

def q116 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 7, 4, 12, 18, 19, 6, 10, 13, 5, 20, 2, 16, 8, 14, 3, 15, 17, 11]
    [0, 1, 13, 17, 4, 11, 8, 3, 15, 2, 9, 20, 5, 10, 16, 18, 14, 19, 6, 7, 12] (by decide) (by decide)

def q117 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 14, 3, 11, 17, 18, 5, 6, 9, 12, 4, 19, 2, 15, 13, 10, 20, 1, 16, 7]
    [0, 18, 13, 3, 11, 7, 8, 20, 1, 9, 16, 4, 10, 15, 2, 14, 19, 5, 6, 12, 17] (by decide) (by decide)

theorem c_3_9 : P 19 (9 : Fin 21) :=
  ⟨23, by decide, q116, q117, by decide +kernel, by decide +kernel⟩

def q118 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 10, 3, 4, 6, 5, 17, 12, 9, 2, 18, 8, 13, 16, 20, 14, 7, 11, 19, 15]
    [0, 1, 10, 3, 4, 6, 5, 17, 12, 9, 2, 18, 8, 13, 16, 20, 14, 7, 11, 19, 15] (by decide) (by decide)

def q119 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 6, 10, 3, 11, 5, 1, 17, 8, 9, 2, 4, 13, 12, 16, 19, 14, 7, 18, 15, 20]
    [0, 6, 10, 3, 11, 5, 1, 17, 8, 9, 2, 4, 13, 12, 16, 19, 14, 7, 18, 15, 20] (by decide) (by decide)

theorem c_3_10 : P 19 (10 : Fin 21) :=
  ⟨23, by decide, q118, q119, by decide +kernel, by decide +kernel⟩

theorem c_3_11 : P 19 (11 : Fin 21) :=
  ⟨23, by decide, q92, q93, by decide +kernel, by decide +kernel⟩

theorem c_3_12 : P 19 (12 : Fin 21) :=
  ⟨23, by decide, q94, q95, by decide +kernel, by decide +kernel⟩

def q120 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 13, 5, 4, 11, 7, 20, 15, 2, 10, 3, 17, 9, 14, 19, 16, 18, 12, 8, 6]
    [0, 1, 9, 11, 4, 3, 20, 6, 19, 13, 10, 5, 18, 2, 14, 8, 16, 12, 17, 15, 7] (by decide) (by decide)

def q121 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 12, 4, 11, 7, 6, 20, 1, 9, 10, 3, 16, 14, 19, 15, 2, 17, 8, 13, 5]
    [0, 8, 16, 11, 3, 20, 6, 5, 18, 9, 10, 4, 2, 19, 13, 15, 12, 17, 1, 14, 7] (by decide) (by decide)

theorem c_3_13 : P 19 (13 : Fin 21) :=
  ⟨23, by decide, q120, q121, by decide +kernel, by decide +kernel⟩

def q122 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 1, 12, 11, 5, 9, 4, 14, 19, 13, 16, 20, 18, 7, 17, 8, 15, 3, 6, 10]
    [0, 2, 1, 18, 7, 5, 19, 14, 16, 6, 20, 4, 3, 10, 8, 17, 11, 15, 13, 9, 12] (by decide) (by decide)

def q123 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 1, 8, 11, 10, 5, 9, 0, 19, 18, 12, 16, 4, 14, 3, 13, 15, 20, 2, 6, 17]
    [7, 1, 18, 14, 12, 5, 19, 0, 2, 6, 4, 3, 10, 15, 13, 16, 11, 20, 9, 8, 17] (by decide) (by decide)

theorem c_3_14 : P 19 (14 : Fin 21) :=
  ⟨389, by decide, q122, q123, by decide +kernel, by decide +kernel⟩

def q124 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 15, 7, 4, 5, 9, 3, 20, 6, 12, 13, 10, 11, 16, 2, 14, 17, 18, 19, 8]
    [0, 1, 15, 7, 4, 5, 9, 3, 20, 6, 12, 13, 10, 11, 16, 2, 14, 17, 18, 19, 8] (by decide) (by decide)

def q125 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 14, 3, 4, 5, 8, 20, 6, 11, 12, 9, 10, 16, 2, 19, 13, 17, 18, 15, 7]
    [0, 1, 14, 3, 4, 5, 8, 20, 6, 11, 12, 9, 10, 16, 2, 19, 13, 17, 18, 15, 7] (by decide) (by decide)

theorem c_3_15 : P 19 (15 : Fin 21) :=
  ⟨23, by decide, q124, q125, by decide +kernel, by decide +kernel⟩

theorem c_3_16 : P 19 (16 : Fin 21) :=
  ⟨389, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

def q126 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 17, 6, 4, 2, 8, 12, 10, 7, 3, 18, 20, 19, 16, 5, 14, 15, 13, 11, 9]
    [0, 1, 5, 10, 4, 15, 3, 9, 6, 20, 8, 19, 7, 18, 16, 17, 14, 2, 11, 13, 12] (by decide) (by decide)

def q127 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 13, 11, 9, 7, 8, 17, 6, 3, 2, 4, 19, 15, 12, 10, 14, 20, 18, 16, 5]
    [0, 1, 10, 9, 11, 20, 8, 5, 6, 4, 15, 3, 14, 2, 16, 13, 19, 7, 18, 12, 17] (by decide) (by decide)

theorem c_3_17 : P 19 (17 : Fin 21) :=
  ⟨23, by decide, q126, q127, by decide +kernel, by decide +kernel⟩

theorem c_3_18 : P 19 (18 : Fin 21) :=
  ⟨23, by decide, q106, q107, by decide +kernel, by decide +kernel⟩

theorem c_3_19 : P 19 (19 : Fin 21) :=
  ⟨23, by decide, q108, q109, by decide +kernel, by decide +kernel⟩

theorem c_3_20 : P 19 (20 : Fin 21) :=
  ⟨23, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_4_0 : P 7 (0 : Fin 21) :=
  ⟨7, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_4_1 : P 7 (1 : Fin 21) :=
  ⟨7, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_4_2 : P 7 (2 : Fin 21) :=
  ⟨7, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_4_3 : P 7 (3 : Fin 21) :=
  ⟨15, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_4_4 : P 7 (4 : Fin 21) :=
  ⟨23, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q128 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 2, 0, 3, 5, 7, 20, 14, 16, 6, 19, 4, 18, 9, 17, 8, 15, 11, 13, 10, 12]
    [2, 0, 1, 3, 11, 4, 9, 5, 15, 13, 19, 17, 20, 18, 7, 16, 8, 14, 12, 10, 6] (by decide) (by decide)

def q129 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 7, 20, 10, 12, 6, 19, 0, 2, 5, 3, 4, 14, 16, 13, 15, 11, 18, 9, 17, 8]
    [7, 0, 8, 10, 11, 9, 5, 1, 20, 18, 3, 16, 4, 14, 12, 15, 13, 19, 17, 6, 2] (by decide) (by decide)

theorem c_4_5 : P 7 (5 : Fin 21) :=
  ⟨23, by decide, q128, q129, by decide +kernel, by decide +kernel⟩

def q130 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 6, 4, 17, 18, 11, 7, 10, 13, 8, 20, 9, 14, 5, 16, 15, 3, 12, 19]
    [0, 1, 2, 18, 4, 15, 3, 8, 11, 13, 9, 7, 19, 10, 14, 17, 16, 5, 6, 20, 12] (by decide) (by decide)

def q131 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 11, 3, 17, 18, 7, 6, 9, 13, 4, 16, 14, 10, 12, 15, 20, 8, 19, 5]
    [0, 1, 2, 4, 11, 20, 8, 7, 18, 9, 14, 3, 15, 10, 13, 16, 12, 5, 6, 19, 17] (by decide) (by decide)

theorem c_4_6 : P 7 (6 : Fin 21) :=
  ⟨15, by decide, q130, q131, by decide +kernel, by decide +kernel⟩

theorem c_4_7 : P 7 (7 : Fin 21) :=
  ⟨23, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

def q132 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 1, 6, 8, 15, 20, 14, 16, 3, 12, 4, 18, 9, 11, 5, 7, 17, 10, 13, 19]
    [0, 2, 1, 9, 11, 15, 3, 16, 4, 13, 18, 14, 10, 19, 7, 5, 8, 17, 12, 20, 6] (by decide) (by decide)

def q133 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 1, 6, 13, 15, 20, 19, 0, 2, 8, 11, 4, 14, 16, 10, 12, 3, 17, 9, 18, 5]
    [7, 1, 8, 16, 11, 20, 2, 0, 9, 18, 14, 10, 15, 3, 12, 4, 13, 17, 19, 6, 5] (by decide) (by decide)

theorem c_4_8 : P 7 (8 : Fin 21) :=
  ⟨23, by decide, q132, q133, by decide +kernel, by decide +kernel⟩

def q134 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 9, 14, 17, 10, 7, 8, 12, 20, 11, 3, 19, 16, 5, 4, 15, 13, 18, 6]
    [0, 1, 2, 12, 16, 15, 20, 7, 8, 3, 6, 11, 9, 18, 4, 17, 14, 5, 19, 13, 10] (by decide) (by decide)

def q135 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 14, 13, 17, 6, 7, 8, 19, 16, 10, 3, 15, 12, 4, 11, 20, 18, 2, 5]
    [0, 1, 19, 12, 15, 20, 6, 7, 8, 2, 11, 16, 14, 4, 3, 13, 10, 5, 18, 9, 17] (by decide) (by decide)

theorem c_4_9 : P 7 (9 : Fin 21) :=
  ⟨15, by decide, q134, q135, by decide +kernel, by decide +kernel⟩

def q136 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 10, 14, 15, 13, 11, 7, 20, 19, 8, 6, 12, 16, 17, 4, 5, 9, 3, 18]
    [0, 1, 2, 19, 16, 17, 12, 8, 11, 18, 3, 7, 13, 6, 4, 5, 14, 15, 20, 10, 9] (by decide) (by decide)

def q137 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 10, 14, 20, 18, 7, 6, 19, 15, 13, 11, 12, 16, 3, 4, 5, 8, 2, 17]
    [0, 1, 19, 15, 16, 17, 8, 7, 18, 2, 3, 12, 13, 11, 4, 10, 14, 20, 6, 9, 5] (by decide) (by decide)

theorem c_4_10 : P 7 (10 : Fin 21) :=
  ⟨15, by decide, q136, q137, by decide +kernel, by decide +kernel⟩

def q138 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 1, 3, 11, 17, 12, 14, 16, 18, 19, 4, 6, 13, 7, 15, 8, 5, 9, 10, 20]
    [0, 2, 1, 3, 11, 17, 12, 14, 16, 18, 19, 4, 6, 13, 7, 15, 8, 5, 9, 10, 20] (by decide) (by decide)

def q139 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 1, 8, 10, 16, 17, 19, 0, 2, 18, 3, 11, 13, 12, 14, 15, 4, 5, 9, 6, 20]
    [7, 1, 8, 10, 16, 17, 19, 0, 2, 18, 3, 11, 13, 12, 14, 15, 4, 5, 9, 6, 20] (by decide) (by decide)

theorem c_4_11 : P 7 (11 : Fin 21) :=
  ⟨23, by decide, q138, q139, by decide +kernel, by decide +kernel⟩

def q140 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 12, 4, 5, 19, 11, 8, 9, 13, 7, 3, 10, 16, 17, 14, 15, 20, 6, 18]
    [0, 1, 2, 12, 4, 5, 19, 11, 8, 9, 13, 7, 3, 10, 16, 17, 14, 15, 20, 6, 18] (by decide) (by decide)

def q141 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 19, 11, 4, 5, 18, 7, 8, 9, 12, 3, 10, 15, 16, 13, 14, 20, 6, 2, 17]
    [0, 1, 19, 11, 4, 5, 18, 7, 8, 9, 12, 3, 10, 15, 16, 13, 14, 20, 6, 2, 17] (by decide) (by decide)

theorem c_4_12 : P 7 (12 : Fin 21) :=
  ⟨15, by decide, q140, q141, by decide +kernel, by decide +kernel⟩

def q142 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 13, 14, 5, 9, 8, 11, 19, 12, 7, 18, 20, 16, 15, 4, 17, 10, 6, 3]
    [0, 1, 2, 20, 16, 5, 19, 11, 7, 6, 18, 8, 10, 3, 4, 15, 14, 17, 12, 9, 13] (by decide) (by decide)

def q143 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 13, 10, 5, 8, 7, 18, 19, 12, 14, 4, 16, 15, 11, 3, 17, 6, 2, 20]
    [0, 1, 19, 16, 12, 5, 18, 7, 6, 2, 4, 15, 10, 3, 11, 14, 13, 17, 8, 9, 20] (by decide) (by decide)

theorem c_4_13 : P 7 (13 : Fin 21) :=
  ⟨15, by decide, q142, q143, by decide +kernel, by decide +kernel⟩

theorem c_4_14 : P 7 (14 : Fin 21) :=
  ⟨23, by decide, q98, q99, by decide +kernel, by decide +kernel⟩

def q144 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 2, 0, 6, 15, 8, 9, 4, 16, 3, 13, 14, 18, 20, 17, 7, 5, 11, 19, 12, 10]
    [2, 0, 1, 9, 7, 16, 3, 15, 5, 6, 20, 17, 19, 10, 11, 4, 8, 14, 12, 18, 13] (by decide) (by decide)

def q145 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 7, 5, 11, 15, 8, 9, 0, 2, 20, 13, 14, 4, 16, 3, 12, 10, 18, 19, 17, 6]
    [7, 0, 8, 14, 12, 2, 20, 1, 5, 6, 16, 3, 15, 10, 11, 4, 13, 19, 17, 18, 9] (by decide) (by decide)

theorem c_4_15 : P 7 (15 : Fin 21) :=
  ⟨23, by decide, q144, q145, by decide +kernel, by decide +kernel⟩

theorem c_4_16 : P 7 (16 : Fin 21) :=
  ⟨23, by decide, q102, q103, by decide +kernel, by decide +kernel⟩

def q146 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 2, 0, 3, 17, 11, 13, 4, 16, 18, 10, 14, 6, 12, 5, 8, 15, 7, 20, 19, 9]
    [2, 0, 1, 3, 7, 14, 12, 17, 15, 20, 10, 5, 13, 6, 11, 16, 8, 4, 9, 19, 18] (by decide) (by decide)

def q147 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 7, 20, 3, 16, 18, 9, 0, 2, 17, 10, 13, 11, 12, 4, 15, 14, 6, 19, 5, 8]
    [7, 0, 8, 3, 14, 19, 17, 1, 20, 6, 10, 12, 13, 11, 16, 15, 4, 9, 5, 18, 2] (by decide) (by decide)

theorem c_4_17 : P 7 (17 : Fin 21) :=
  ⟨23, by decide, q146, q147, by decide +kernel, by decide +kernel⟩

def q148 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 18, 4, 15, 3, 8, 11, 13, 9, 7, 19, 10, 14, 17, 16, 5, 6, 20, 12]
    [0, 1, 2, 6, 4, 17, 18, 11, 7, 10, 13, 8, 20, 9, 14, 5, 16, 15, 3, 12, 19] (by decide) (by decide)

def q149 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 4, 11, 20, 8, 7, 18, 9, 14, 3, 15, 10, 13, 16, 12, 5, 6, 19, 17]
    [0, 1, 2, 11, 3, 17, 18, 7, 6, 9, 13, 4, 16, 14, 10, 12, 15, 20, 8, 19, 5] (by decide) (by decide)

theorem c_4_18 : P 7 (18 : Fin 21) :=
  ⟨15, by decide, q148, q149, by decide +kernel, by decide +kernel⟩

def q150 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 19, 4, 15, 20, 7, 11, 13, 10, 8, 18, 9, 16, 5, 14, 17, 12, 3, 6]
    [0, 1, 2, 19, 4, 15, 20, 7, 11, 13, 10, 8, 18, 9, 16, 5, 14, 17, 12, 3, 6] (by decide) (by decide)

def q151 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 19, 3, 11, 20, 6, 7, 18, 9, 15, 4, 14, 16, 12, 10, 13, 17, 8, 2, 5]
    [0, 1, 19, 3, 11, 20, 6, 7, 18, 9, 15, 4, 14, 16, 12, 10, 13, 17, 8, 2, 5] (by decide) (by decide)

theorem c_4_19 : P 7 (19 : Fin 21) :=
  ⟨15, by decide, q150, q151, by decide +kernel, by decide +kernel⟩

def q152 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 20, 4, 17, 12, 8, 7, 10, 9, 11, 6, 13, 16, 15, 14, 5, 19, 18, 3]
    [0, 1, 2, 20, 4, 17, 12, 8, 7, 10, 9, 11, 6, 13, 16, 15, 14, 5, 19, 18, 3] (by decide) (by decide)

def q153 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 19, 4, 3, 17, 8, 7, 6, 9, 16, 11, 13, 12, 15, 14, 10, 5, 18, 2, 20]
    [0, 1, 19, 4, 3, 17, 8, 7, 6, 9, 16, 11, 13, 12, 15, 14, 10, 5, 18, 2, 20] (by decide) (by decide)

theorem c_4_20 : P 7 (20 : Fin 21) :=
  ⟨15, by decide, q152, q153, by decide +kernel, by decide +kernel⟩

theorem c_5_0 : P 389 (0 : Fin 21) :=
  ⟨389, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q154 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 2, 13, 16, 17, 10, 7, 11, 18, 6, 8, 19, 3, 14, 15, 4, 5, 9, 12, 20]
    [0, 1, 2, 13, 16, 17, 10, 7, 11, 18, 6, 8, 19, 3, 14, 15, 4, 5, 9, 12, 20] (by decide) (by decide)

def q155 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 1, 9, 12, 16, 17, 6, 7, 18, 2, 13, 15, 3, 10, 14, 11, 4, 5, 8, 19, 20]
    [0, 1, 9, 12, 16, 17, 6, 7, 18, 2, 13, 15, 3, 10, 14, 11, 4, 5, 8, 19, 20] (by decide) (by decide)

theorem c_5_1 : P 389 (1 : Fin 21) :=
  ⟨6799, by decide, q154, q155, by decide +kernel, by decide +kernel⟩

theorem c_5_2 : P 389 (2 : Fin 21) :=
  ⟨389, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q156 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 3, 2, 5, 13, 18, 17, 7, 11, 10, 4, 8, 14, 9, 20, 6, 15, 16, 1, 12, 19]
    [0, 18, 2, 1, 10, 3, 15, 7, 11, 13, 9, 8, 19, 4, 12, 16, 17, 6, 5, 20, 14] (by decide) (by decide)

def q157 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 2, 1, 12, 18, 17, 3, 7, 10, 9, 4, 13, 14, 16, 6, 11, 15, 0, 8, 19, 5]
    [17, 2, 1, 6, 10, 20, 14, 7, 18, 9, 8, 15, 3, 11, 12, 16, 13, 5, 4, 19, 0] (by decide) (by decide)

theorem c_5_3 : P 389 (3 : Fin 21) :=
  ⟨6799, by decide, q156, q157, by decide +kernel, by decide +kernel⟩

def q158 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 4, 2, 6, 1, 13, 3, 7, 11, 15, 17, 8, 12, 5, 14, 9, 16, 10, 18, 20, 19]
    [0, 4, 2, 6, 1, 13, 3, 7, 11, 15, 17, 8, 12, 5, 14, 9, 16, 10, 18, 20, 19] (by decide) (by decide)

def q159 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 9, 2, 6, 18, 20, 3, 7, 11, 1, 13, 8, 12, 10, 14, 16, 15, 17, 4, 19, 5]
    [0, 9, 2, 6, 18, 20, 3, 7, 11, 1, 13, 8, 12, 10, 14, 16, 15, 17, 4, 19, 5] (by decide) (by decide)

theorem c_5_4 : P 389 (4 : Fin 21) :=
  ⟨6799, by decide, q158, q159, by decide +kernel, by decide +kernel⟩

theorem c_5_5 : P 389 (5 : Fin 21) :=
  ⟨6799, by decide, q156, q157, by decide +kernel, by decide +kernel⟩

theorem c_5_6 : P 389 (6 : Fin 21) :=
  ⟨6799, by decide, q158, q159, by decide +kernel, by decide +kernel⟩

theorem c_5_7 : P 389 (7 : Fin 21) :=
  ⟨389, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_5_8 : P 389 (8 : Fin 21) :=
  ⟨389, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q160 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 9, 2, 16, 5, 10, 18, 7, 11, 17, 15, 8, 20, 1, 19, 4, 6, 13, 3, 12, 14]
    [0, 13, 2, 18, 15, 4, 16, 7, 11, 1, 5, 8, 19, 17, 20, 10, 3, 9, 6, 14, 12] (by decide) (by decide)

def q161 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 9, 2, 12, 10, 17, 14, 7, 16, 1, 15, 4, 6, 18, 3, 11, 13, 20, 8, 19, 0]
    [20, 9, 2, 14, 11, 0, 12, 7, 18, 1, 4, 15, 3, 16, 6, 10, 8, 5, 13, 19, 17] (by decide) (by decide)

theorem c_5_9 : P 389 (9 : Fin 21) :=
  ⟨6799, by decide, q160, q161, by decide +kernel, by decide +kernel⟩

theorem c_5_10 : P 389 (10 : Fin 21) :=
  ⟨6799, by decide, q156, q157, by decide +kernel, by decide +kernel⟩

theorem c_5_11 : P 389 (11 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_5_12 : P 389 (12 : Fin 21) :=
  ⟨6799, by decide, q158, q159, by decide +kernel, by decide +kernel⟩

theorem c_5_13 : P 389 (13 : Fin 21) :=
  ⟨6799, by decide, q154, q155, by decide +kernel, by decide +kernel⟩

theorem c_5_14 : P 389 (14 : Fin 21) :=
  ⟨6799, by decide, q156, q157, by decide +kernel, by decide +kernel⟩

theorem c_5_15 : P 389 (15 : Fin 21) :=
  ⟨6799, by decide, q158, q159, by decide +kernel, by decide +kernel⟩

theorem c_5_16 : P 389 (16 : Fin 21) :=
  ⟨6799, by decide, q160, q161, by decide +kernel, by decide +kernel⟩

theorem c_5_17 : P 389 (17 : Fin 21) :=
  ⟨6799, by decide, q160, q161, by decide +kernel, by decide +kernel⟩

theorem c_5_18 : P 389 (18 : Fin 21) :=
  ⟨6799, by decide, q154, q155, by decide +kernel, by decide +kernel⟩

theorem c_5_19 : P 389 (19 : Fin 21) :=
  ⟨6799, by decide, q154, q155, by decide +kernel, by decide +kernel⟩

theorem c_5_20 : P 389 (20 : Fin 21) :=
  ⟨6799, by decide, q160, q161, by decide +kernel, by decide +kernel⟩

theorem c_6_0 : P 23 (0 : Fin 21) :=
  ⟨23, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_6_1 : P 23 (1 : Fin 21) :=
  ⟨23, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_6_2 : P 23 (2 : Fin 21) :=
  ⟨23, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_6_3 : P 23 (3 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_6_4 : P 23 (4 : Fin 21) :=
  ⟨23, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_6_5 : P 23 (5 : Fin 21) :=
  ⟨1371, by decide, q82, q83, by decide +kernel, by decide +kernel⟩

theorem c_6_6 : P 23 (6 : Fin 21) :=
  ⟨31, by decide, q130, q131, by decide +kernel, by decide +kernel⟩

def q162 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 0, 20, 2, 4, 3, 12, 10, 7, 8, 18, 6, 11, 5, 16, 15, 14, 13, 19, 9, 17]
    [1, 0, 3, 5, 4, 13, 11, 8, 9, 19, 7, 12, 6, 17, 16, 15, 14, 20, 10, 18, 2] (by decide) (by decide)

def q163 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 20, 19, 9, 3, 8, 17, 6, 7, 4, 2, 11, 10, 12, 15, 14, 13, 18, 5, 16, 1]
    [0, 20, 10, 4, 9, 18, 7, 8, 5, 3, 12, 11, 13, 16, 15, 14, 19, 6, 17, 2, 1] (by decide) (by decide)

theorem c_6_7 : P 23 (7 : Fin 21) :=
  ⟨1371, by decide, q162, q163, by decide +kernel, by decide +kernel⟩

def q164 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 0, 3, 2, 4, 20, 6, 9, 8, 7, 19, 12, 11, 17, 14, 15, 16, 13, 18, 10, 5]
    [1, 0, 3, 2, 4, 20, 6, 9, 8, 7, 19, 12, 11, 17, 14, 15, 16, 13, 18, 10, 5] (by decide) (by decide)

def q165 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 20, 2, 9, 4, 6, 5, 8, 7, 3, 19, 11, 16, 13, 14, 15, 12, 18, 17, 10, 1]
    [0, 20, 2, 9, 4, 6, 5, 8, 7, 3, 19, 11, 16, 13, 14, 15, 12, 18, 17, 10, 1] (by decide) (by decide)

theorem c_6_8 : P 23 (8 : Fin 21) :=
  ⟨1371, by decide, q164, q165, by decide +kernel, by decide +kernel⟩

def q166 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 4, 6, 2, 1, 12, 18, 5, 9, 10, 20, 19, 13, 7, 14, 11, 16, 15, 3, 17, 8]
    [0, 4, 3, 18, 1, 7, 2, 13, 20, 8, 9, 15, 5, 12, 14, 17, 16, 19, 6, 11, 10] (by decide) (by decide)

def q167 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 11, 2, 1, 8, 17, 4, 5, 9, 6, 19, 18, 12, 14, 10, 16, 15, 20, 3, 13, 7]
    [0, 3, 2, 18, 6, 7, 9, 20, 4, 8, 14, 1, 12, 19, 13, 16, 15, 5, 11, 10, 17] (by decide) (by decide)

theorem c_6_9 : P 23 (9 : Fin 21) :=
  ⟨1371, by decide, q166, q167, by decide +kernel, by decide +kernel⟩

def q168 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 4, 18, 2, 1, 20, 3, 17, 10, 13, 19, 12, 9, 11, 14, 8, 16, 5, 6, 15, 7]
    [0, 4, 3, 6, 1, 17, 18, 20, 15, 12, 8, 13, 11, 9, 14, 19, 16, 7, 2, 10, 5] (by decide) (by decide)

def q169 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 4, 2, 1, 6, 20, 3, 17, 9, 18, 19, 8, 16, 10, 13, 15, 12, 5, 11, 14, 7]
    [0, 3, 2, 6, 1, 17, 4, 20, 11, 8, 13, 18, 16, 14, 19, 15, 12, 7, 9, 10, 5] (by decide) (by decide)

theorem c_6_10 : P 23 (10 : Fin 21) :=
  ⟨1371, by decide, q168, q169, by decide +kernel, by decide +kernel⟩

def q170 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 0, 18, 2, 4, 12, 3, 13, 11, 8, 20, 19, 7, 5, 14, 17, 16, 10, 6, 9, 15]
    [1, 0, 3, 6, 4, 13, 18, 12, 9, 19, 17, 8, 5, 7, 14, 20, 16, 15, 2, 11, 10] (by decide) (by decide)

def q171 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 17, 2, 9, 11, 8, 20, 18, 7, 4, 19, 3, 12, 10, 13, 16, 15, 6, 5, 14, 1]
    [0, 20, 2, 11, 9, 18, 17, 8, 5, 3, 13, 4, 12, 14, 19, 16, 15, 1, 7, 10, 6] (by decide) (by decide)

theorem c_6_11 : P 23 (11 : Fin 21) :=
  ⟨1371, by decide, q170, q171, by decide +kernel, by decide +kernel⟩

theorem c_6_12 : P 23 (12 : Fin 21) :=
  ⟨31, by decide, q140, q141, by decide +kernel, by decide +kernel⟩

def q172 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 4, 3, 2, 1, 19, 6, 15, 13, 9, 12, 20, 10, 8, 14, 7, 16, 17, 18, 5, 11]
    [0, 4, 3, 2, 1, 19, 6, 15, 13, 9, 12, 20, 10, 8, 14, 7, 16, 17, 18, 5, 11] (by decide) (by decide)

def q173 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 3, 2, 1, 18, 5, 11, 20, 9, 8, 19, 6, 15, 13, 14, 12, 16, 17, 4, 10, 7]
    [0, 3, 2, 1, 18, 5, 11, 20, 9, 8, 19, 6, 15, 13, 14, 12, 16, 17, 4, 10, 7] (by decide) (by decide)

theorem c_6_13 : P 23 (13 : Fin 21) :=
  ⟨1371, by decide, q172, q173, by decide +kernel, by decide +kernel⟩

theorem c_6_14 : P 23 (14 : Fin 21) :=
  ⟨6799, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_6_15 : P 23 (15 : Fin 21) :=
  ⟨1371, by decide, q78, q79, by decide +kernel, by decide +kernel⟩

theorem c_6_16 : P 23 (16 : Fin 21) :=
  ⟨6799, by decide, q122, q123, by decide +kernel, by decide +kernel⟩

theorem c_6_17 : P 23 (17 : Fin 21) :=
  ⟨1371, by decide, q106, q107, by decide +kernel, by decide +kernel⟩

theorem c_6_18 : P 23 (18 : Fin 21) :=
  ⟨31, by decide, q148, q149, by decide +kernel, by decide +kernel⟩

theorem c_6_19 : P 23 (19 : Fin 21) :=
  ⟨31, by decide, q150, q151, by decide +kernel, by decide +kernel⟩

theorem c_6_20 : P 23 (20 : Fin 21) :=
  ⟨31, by decide, q152, q153, by decide +kernel, by decide +kernel⟩

theorem c_7_0 : P 15 (0 : Fin 21) :=
  ⟨15, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_7_1 : P 15 (1 : Fin 21) :=
  ⟨15, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_7_2 : P 15 (2 : Fin 21) :=
  ⟨15, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_7_3 : P 15 (3 : Fin 21) :=
  ⟨15, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_7_4 : P 15 (4 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_7_5 : P 15 (5 : Fin 21) :=
  ⟨31, by decide, q128, q129, by decide +kernel, by decide +kernel⟩

def q174 : Equiv.Perm (Fin 21) :=
  mkPerm [2, 3, 0, 1, 6, 13, 4, 7, 8, 9, 19, 11, 12, 5, 18, 15, 16, 20, 14, 10, 17]
    [2, 3, 0, 1, 6, 13, 4, 7, 8, 9, 19, 11, 12, 5, 18, 15, 16, 20, 14, 10, 17] (by decide) (by decide)

def q175 : Equiv.Perm (Fin 21) :=
  mkPerm [2, 20, 0, 6, 13, 9, 3, 7, 8, 5, 18, 11, 12, 4, 14, 15, 16, 19, 10, 17, 1]
    [2, 20, 0, 6, 13, 9, 3, 7, 8, 5, 18, 11, 12, 4, 14, 15, 16, 19, 10, 17, 1] (by decide) (by decide)

theorem c_7_6 : P 15 (6 : Fin 21) :=
  ⟨31, by decide, q174, q175, by decide +kernel, by decide +kernel⟩

theorem c_7_7 : P 15 (7 : Fin 21) :=
  ⟨31, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

def q176 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 8, 20, 1, 2, 18, 10, 15, 3, 12, 19, 13, 9, 14, 11, 4, 7, 5, 6, 17, 16]
    [0, 3, 4, 8, 15, 17, 18, 16, 1, 12, 6, 14, 9, 11, 13, 7, 20, 19, 5, 10, 2] (by decide) (by decide)

def q177 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 4, 6, 1, 2, 17, 15, 20, 8, 19, 18, 9, 14, 10, 11, 3, 12, 5, 13, 16, 0]
    [20, 3, 4, 15, 1, 17, 2, 0, 8, 11, 13, 14, 16, 18, 12, 6, 19, 5, 10, 9, 7] (by decide) (by decide)

theorem c_7_8 : P 15 (8 : Fin 21) :=
  ⟨1371, by decide, q176, q177, by decide +kernel, by decide +kernel⟩

def q178 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 3, 0, 2, 9, 20, 7, 4, 16, 6, 19, 14, 18, 5, 12, 15, 8, 13, 11, 10, 17]
    [2, 0, 3, 1, 7, 13, 9, 6, 16, 4, 19, 18, 14, 17, 11, 15, 8, 20, 12, 10, 5] (by decide) (by decide)

def q179 : Equiv.Perm (Fin 21) :=
  mkPerm [8, 20, 7, 9, 16, 6, 3, 0, 2, 5, 19, 14, 4, 12, 11, 15, 13, 18, 10, 17, 1]
    [7, 20, 8, 6, 12, 9, 5, 2, 0, 3, 18, 14, 13, 16, 11, 15, 4, 19, 17, 10, 1] (by decide) (by decide)

theorem c_7_9 : P 15 (9 : Fin 21) :=
  ⟨31, by decide, q178, q179, by decide +kernel, by decide +kernel⟩

def q180 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 12, 1, 2, 13, 3, 17, 10, 20, 19, 18, 6, 14, 11, 16, 8, 5, 9, 15, 4]
    [0, 3, 4, 6, 20, 17, 12, 1, 16, 18, 8, 14, 2, 5, 13, 19, 15, 7, 11, 10, 9] (by decide) (by decide)

def q181 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 12, 8, 1, 9, 20, 3, 17, 6, 19, 18, 2, 13, 10, 16, 15, 4, 5, 14, 11, 0]
    [20, 3, 11, 6, 16, 17, 8, 0, 2, 4, 13, 19, 1, 12, 18, 15, 14, 7, 10, 9, 5] (by decide) (by decide)

theorem c_7_10 : P 15 (10 : Fin 21) :=
  ⟨1369, by decide, q180, q181, by decide +kernel, by decide +kernel⟩

theorem c_7_11 : P 15 (11 : Fin 21) :=
  ⟨31, by decide, q138, q139, by decide +kernel, by decide +kernel⟩

def q182 : Equiv.Perm (Fin 21) :=
  mkPerm [1, 3, 0, 2, 12, 13, 11, 14, 16, 18, 10, 4, 6, 17, 9, 15, 8, 20, 7, 19, 5]
    [2, 0, 3, 1, 11, 20, 12, 18, 16, 14, 10, 6, 4, 5, 7, 15, 8, 13, 9, 19, 17] (by decide) (by decide)

def q183 : Equiv.Perm (Fin 21) :=
  mkPerm [8, 20, 7, 19, 12, 18, 10, 0, 2, 17, 9, 11, 13, 16, 14, 15, 4, 6, 3, 5, 1]
    [7, 20, 8, 18, 16, 19, 17, 2, 0, 10, 6, 11, 4, 12, 14, 15, 13, 9, 5, 3, 1] (by decide) (by decide)

theorem c_7_12 : P 15 (12 : Fin 21) :=
  ⟨31, by decide, q182, q183, by decide +kernel, by decide +kernel⟩

theorem c_7_13 : P 15 (13 : Fin 21) :=
  ⟨31, by decide, q42, q43, by decide +kernel, by decide +kernel⟩

theorem c_7_14 : P 15 (14 : Fin 21) :=
  ⟨31, by decide, q98, q99, by decide +kernel, by decide +kernel⟩

def q184 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 15, 7, 1, 3, 18, 10, 8, 2, 17, 19, 11, 5, 4, 13, 14, 20, 9, 6, 12, 16]
    [0, 3, 8, 4, 13, 12, 18, 2, 7, 17, 6, 11, 19, 14, 15, 1, 20, 9, 5, 10, 16] (by decide) (by decide)

def q185 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 14, 6, 8, 2, 17, 15, 7, 1, 3, 18, 10, 4, 9, 13, 19, 16, 5, 11, 12, 0]
    [20, 8, 4, 9, 12, 17, 2, 7, 3, 13, 11, 18, 19, 14, 1, 6, 16, 5, 10, 15, 0] (by decide) (by decide)

theorem c_7_15 : P 15 (15 : Fin 21) :=
  ⟨1371, by decide, q184, q185, by decide +kernel, by decide +kernel⟩

def q186 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 16, 13, 2, 1, 12, 10, 15, 3, 18, 19, 20, 6, 11, 14, 7, 4, 5, 9, 17, 8]
    [0, 4, 3, 8, 16, 17, 12, 15, 20, 18, 6, 13, 5, 2, 14, 7, 1, 19, 9, 10, 11] (by decide) (by decide)

def q187 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 12, 9, 1, 8, 17, 15, 20, 2, 18, 19, 6, 11, 10, 14, 3, 4, 5, 16, 13, 7]
    [0, 3, 8, 15, 16, 17, 11, 20, 4, 2, 13, 12, 1, 19, 14, 6, 18, 5, 9, 10, 7] (by decide) (by decide)

theorem c_7_16 : P 15 (16 : Fin 21) :=
  ⟨1371, by decide, q186, q187, by decide +kernel, by decide +kernel⟩

theorem c_7_17 : P 15 (17 : Fin 21) :=
  ⟨31, by decide, q146, q147, by decide +kernel, by decide +kernel⟩

def q188 : Equiv.Perm (Fin 21) :=
  mkPerm [2, 3, 0, 1, 18, 20, 14, 11, 8, 12, 10, 7, 9, 17, 6, 15, 16, 13, 4, 19, 5]
    [2, 3, 0, 1, 18, 20, 14, 11, 8, 12, 10, 7, 9, 17, 6, 15, 16, 13, 4, 19, 5] (by decide) (by decide)

def q189 : Equiv.Perm (Fin 21) :=
  mkPerm [2, 20, 0, 18, 4, 19, 10, 7, 8, 17, 6, 14, 16, 13, 11, 15, 12, 9, 3, 5, 1]
    [2, 20, 0, 18, 4, 19, 10, 7, 8, 17, 6, 14, 16, 13, 11, 15, 12, 9, 3, 5, 1] (by decide) (by decide)

theorem c_7_18 : P 15 (18 : Fin 21) :=
  ⟨31, by decide, q188, q189, by decide +kernel, by decide +kernel⟩

theorem c_7_19 : P 15 (19 : Fin 21) :=
  ⟨1369, by decide, q180, q181, by decide +kernel, by decide +kernel⟩

def q190 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 3, 1, 2, 20, 9, 5, 14, 16, 6, 10, 4, 18, 7, 13, 8, 15, 12, 17, 19, 11]
    [0, 2, 3, 1, 11, 6, 9, 13, 15, 5, 10, 20, 17, 14, 7, 16, 8, 18, 12, 19, 4] (by decide) (by decide)

def q191 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 8, 1, 19, 16, 5, 10, 0, 2, 6, 9, 4, 14, 12, 13, 15, 11, 17, 3, 18, 7]
    [7, 2, 8, 18, 11, 5, 9, 20, 1, 10, 6, 16, 13, 14, 12, 15, 4, 17, 19, 3, 0] (by decide) (by decide)

theorem c_7_20 : P 15 (20 : Fin 21) :=
  ⟨31, by decide, q190, q191, by decide +kernel, by decide +kernel⟩

theorem c_8_0 : P 31 (0 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_8_1 : P 31 (1 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_8_2 : P 31 (2 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_8_3 : P 31 (3 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_8_4 : P 31 (4 : Fin 21) :=
  ⟨31, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_8_5 : P 31 (5 : Fin 21) :=
  ⟨1371, by decide, q82, q83, by decide +kernel, by decide +kernel⟩

theorem c_8_6 : P 31 (6 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q192 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 1, 3, 5, 18, 12, 14, 4, 17, 2, 16, 7, 15, 6, 13, 9, 11, 8, 10, 20]
    [0, 2, 10, 3, 8, 4, 14, 12, 18, 16, 19, 17, 6, 15, 7, 13, 11, 9, 5, 1, 20] (by decide) (by decide)

def q193 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 18, 8, 10, 4, 17, 19, 0, 3, 1, 2, 12, 14, 11, 13, 9, 16, 7, 15, 6, 20]
    [7, 9, 10, 8, 4, 0, 19, 17, 2, 15, 3, 13, 11, 14, 12, 18, 16, 5, 1, 6, 20] (by decide) (by decide)

theorem c_8_7 : P 31 (7 : Fin 21) :=
  ⟨5501, by decide, q192, q193, by decide +kernel, by decide +kernel⟩

theorem c_8_8 : P 31 (8 : Fin 21) :=
  ⟨5501, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

def q194 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 10, 1, 9, 18, 20, 3, 14, 4, 13, 11, 16, 2, 19, 17, 6, 12, 7, 8, 15, 5]
    [0, 2, 12, 6, 8, 20, 15, 17, 18, 3, 1, 10, 16, 9, 7, 19, 11, 14, 4, 13, 5] (by decide) (by decide)

def q195 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 6, 8, 14, 4, 20, 10, 0, 9, 18, 16, 2, 19, 3, 13, 11, 12, 7, 15, 1, 5]
    [7, 19, 11, 13, 4, 20, 1, 17, 2, 8, 6, 15, 16, 14, 3, 18, 10, 0, 9, 12, 5] (by decide) (by decide)

theorem c_8_9 : P 31 (9 : Fin 21) :=
  ⟨5501, by decide, q194, q195, by decide +kernel, by decide +kernel⟩

theorem c_8_10 : P 31 (10 : Fin 21) :=
  ⟨1371, by decide, q168, q169, by decide +kernel, by decide +kernel⟩

theorem c_8_11 : P 31 (11 : Fin 21) :=
  ⟨1371, by decide, q170, q171, by decide +kernel, by decide +kernel⟩

theorem c_8_12 : P 31 (12 : Fin 21) :=
  ⟨1371, by decide, q82, q83, by decide +kernel, by decide +kernel⟩

theorem c_8_13 : P 31 (13 : Fin 21) :=
  ⟨5501, by decide, q56, q57, by decide +kernel, by decide +kernel⟩

theorem c_8_14 : P 31 (14 : Fin 21) :=
  ⟨6799, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

def q196 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 9, 1, 2, 19, 3, 15, 14, 4, 13, 18, 16, 10, 11, 6, 8, 5, 12, 17, 20, 7]
    [0, 2, 3, 5, 8, 16, 14, 20, 15, 1, 12, 13, 17, 9, 7, 6, 11, 18, 10, 4, 19] (by decide) (by decide)

def q197 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 8, 1, 19, 3, 20, 14, 0, 9, 18, 2, 15, 10, 11, 13, 4, 12, 17, 16, 6, 7]
    [7, 2, 10, 4, 15, 0, 19, 20, 1, 8, 12, 13, 16, 14, 6, 11, 18, 17, 9, 3, 5] (by decide) (by decide)

theorem c_8_15 : P 31 (15 : Fin 21) :=
  ⟨5501, by decide, q196, q197, by decide +kernel, by decide +kernel⟩

theorem c_8_16 : P 31 (16 : Fin 21) :=
  ⟨54781, by decide, q62, q63, by decide +kernel, by decide +kernel⟩

def q198 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 12, 1, 6, 17, 3, 20, 14, 4, 15, 2, 16, 11, 5, 18, 9, 10, 8, 7, 13, 19]
    [0, 2, 10, 5, 8, 13, 3, 18, 17, 15, 16, 12, 1, 19, 7, 9, 11, 4, 14, 20, 6] (by decide) (by decide)

def q199 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 8, 6, 13, 3, 20, 19, 0, 11, 1, 2, 16, 10, 4, 14, 9, 15, 7, 12, 18, 5]
    [7, 9, 10, 4, 13, 20, 2, 17, 1, 15, 12, 8, 18, 3, 14, 16, 11, 0, 19, 6, 5] (by decide) (by decide)

theorem c_8_17 : P 31 (17 : Fin 21) :=
  ⟨5501, by decide, q198, q199, by decide +kernel, by decide +kernel⟩

theorem c_8_18 : P 31 (18 : Fin 21) :=
  ⟨95, by decide, q148, q149, by decide +kernel, by decide +kernel⟩

theorem c_8_19 : P 31 (19 : Fin 21) :=
  ⟨1371, by decide, q168, q169, by decide +kernel, by decide +kernel⟩

theorem c_8_20 : P 31 (20 : Fin 21) :=
  ⟨1371, by decide, q170, q171, by decide +kernel, by decide +kernel⟩

theorem c_9_0 : P 95 (0 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_9_1 : P 95 (1 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_9_2 : P 95 (2 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_9_3 : P 95 (3 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_9_4 : P 95 (4 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_9_5 : P 95 (5 : Fin 21) :=
  ⟨5501, by decide, q56, q57, by decide +kernel, by decide +kernel⟩

theorem c_9_6 : P 95 (6 : Fin 21) :=
  ⟨95, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_9_7 : P 95 (7 : Fin 21) :=
  ⟨54781, by decide, q56, q57, by decide +kernel, by decide +kernel⟩

theorem c_9_8 : P 95 (8 : Fin 21) :=
  ⟨5501, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

def q200 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 1, 2, 9, 18, 17, 4, 14, 12, 3, 16, 20, 8, 6, 11, 5, 13, 15, 10, 7]
    [0, 2, 3, 10, 7, 16, 14, 20, 13, 4, 19, 15, 9, 17, 8, 18, 11, 6, 5, 1, 12] (by decide) (by decide)

def q201 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 18, 1, 9, 14, 17, 3, 0, 19, 8, 2, 16, 4, 13, 11, 10, 12, 20, 15, 6, 7]
    [7, 2, 10, 6, 12, 0, 19, 20, 9, 3, 15, 14, 16, 13, 4, 18, 11, 5, 1, 8, 17] (by decide) (by decide)

theorem c_9_9 : P 95 (9 : Fin 21) :=
  ⟨54781, by decide, q200, q201, by decide +kernel, by decide +kernel⟩

theorem c_9_10 : P 95 (10 : Fin 21) :=
  ⟨5501, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

theorem c_9_11 : P 95 (11 : Fin 21) :=
  ⟨5501, by decide, q198, q199, by decide +kernel, by decide +kernel⟩

theorem c_9_12 : P 95 (12 : Fin 21) :=
  ⟨5501, by decide, q56, q57, by decide +kernel, by decide +kernel⟩

theorem c_9_13 : P 95 (13 : Fin 21) :=
  ⟨5501, by decide, q56, q57, by decide +kernel, by decide +kernel⟩

theorem c_9_14 : P 95 (14 : Fin 21) :=
  ⟨6799, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_9_15 : P 95 (15 : Fin 21) :=
  ⟨54781, by decide, q60, q61, by decide +kernel, by decide +kernel⟩

theorem c_9_16 : P 95 (16 : Fin 21) :=
  ⟨503803, by decide, q106, q107, by decide +kernel, by decide +kernel⟩

theorem c_9_17 : P 95 (17 : Fin 21) :=
  ⟨5501, by decide, q198, q199, by decide +kernel, by decide +kernel⟩

theorem c_9_18 : P 95 (18 : Fin 21) :=
  ⟨6799, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_9_19 : P 95 (19 : Fin 21) :=
  ⟨5501, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

theorem c_9_20 : P 95 (20 : Fin 21) :=
  ⟨5501, by decide, q198, q199, by decide +kernel, by decide +kernel⟩

theorem c_10_0 : P 1369 (0 : Fin 21) :=
  ⟨1369, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_10_1 : P 1369 (1 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q202 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 19, 3, 8, 14, 4, 9, 6, 16, 10, 5, 18, 15, 11, 20, 7, 12, 17, 1, 13]
    [0, 19, 1, 3, 6, 11, 8, 16, 4, 7, 10, 14, 17, 20, 5, 13, 9, 18, 12, 2, 15] (by decide) (by decide)

def q203 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 19, 3, 8, 13, 0, 9, 5, 2, 15, 10, 4, 14, 11, 16, 6, 12, 17, 1, 18, 20]
    [5, 18, 8, 2, 11, 7, 15, 0, 3, 6, 10, 13, 16, 4, 12, 9, 14, 17, 19, 1, 20] (by decide) (by decide)

theorem c_10_2 : P 1369 (2 : Fin 21) :=
  ⟨1371, by decide, q202, q203, by decide +kernel, by decide +kernel⟩

theorem c_10_3 : P 1369 (3 : Fin 21) :=
  ⟨1369, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_10_4 : P 1369 (4 : Fin 21) :=
  ⟨1369, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q204 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 5, 17, 3, 6, 1, 4, 18, 10, 14, 8, 12, 11, 13, 9, 15, 19, 2, 7, 16, 20]
    [0, 5, 17, 3, 6, 1, 4, 18, 10, 14, 8, 12, 11, 13, 9, 15, 19, 2, 7, 16, 20] (by decide) (by decide)

def q205 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 1, 3, 2, 6, 0, 4, 17, 10, 13, 8, 11, 18, 9, 14, 15, 19, 7, 12, 16, 20]
    [5, 1, 3, 2, 6, 0, 4, 17, 10, 13, 8, 11, 18, 9, 14, 15, 19, 7, 12, 16, 20] (by decide) (by decide)

theorem c_10_5 : P 1369 (5 : Fin 21) :=
  ⟨1371, by decide, q204, q205, by decide +kernel, by decide +kernel⟩

theorem c_10_6 : P 1369 (6 : Fin 21) :=
  ⟨1369, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q206 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 7, 16, 3, 8, 5, 6, 1, 4, 19, 10, 14, 17, 15, 11, 13, 2, 12, 18, 9, 20]
    [0, 7, 16, 3, 8, 5, 6, 1, 4, 19, 10, 14, 17, 15, 11, 13, 2, 12, 18, 9, 20] (by decide) (by decide)

def q207 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 12, 2, 8, 4, 5, 6, 0, 3, 15, 10, 13, 1, 11, 18, 9, 19, 17, 14, 16, 20]
    [7, 12, 2, 8, 4, 5, 6, 0, 3, 15, 10, 13, 1, 11, 18, 9, 19, 17, 14, 16, 20] (by decide) (by decide)

theorem c_10_7 : P 1369 (7 : Fin 21) :=
  ⟨1371, by decide, q206, q207, by decide +kernel, by decide +kernel⟩

theorem c_10_8 : P 1369 (8 : Fin 21) :=
  ⟨1369, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q208 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 9, 7, 3, 6, 14, 4, 2, 8, 1, 10, 11, 12, 20, 5, 15, 19, 18, 17, 16, 13]
    [0, 9, 7, 3, 6, 14, 4, 2, 8, 1, 10, 11, 12, 20, 5, 15, 19, 18, 17, 16, 13] (by decide) (by decide)

def q209 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 14, 3, 2, 13, 0, 9, 7, 8, 6, 10, 11, 19, 4, 1, 15, 18, 17, 16, 12, 20]
    [5, 14, 3, 2, 13, 0, 9, 7, 8, 6, 10, 11, 19, 4, 1, 15, 18, 17, 16, 12, 20] (by decide) (by decide)

theorem c_10_9 : P 1369 (9 : Fin 21) :=
  ⟨1371, by decide, q208, q209, by decide +kernel, by decide +kernel⟩

theorem c_10_10 : P 1369 (10 : Fin 21) :=
  ⟨1369, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q210 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 11, 17, 3, 8, 16, 4, 12, 10, 14, 6, 18, 5, 13, 2, 20, 7, 9, 19, 1, 15]
    [0, 19, 14, 3, 6, 12, 10, 16, 4, 17, 8, 1, 7, 13, 9, 20, 5, 2, 11, 18, 15] (by decide) (by decide)

def q211 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 16, 3, 8, 15, 0, 11, 17, 10, 13, 2, 4, 12, 9, 19, 6, 14, 5, 18, 1, 20]
    [5, 19, 10, 2, 11, 17, 15, 0, 3, 13, 8, 6, 12, 9, 16, 4, 1, 7, 18, 14, 20] (by decide) (by decide)

theorem c_10_11 : P 1369 (11 : Fin 21) :=
  ⟨1371, by decide, q210, q211, by decide +kernel, by decide +kernel⟩

def q212 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 12, 7, 3, 10, 16, 4, 11, 8, 1, 6, 2, 9, 20, 18, 13, 17, 5, 19, 14, 15]
    [0, 9, 11, 3, 6, 17, 10, 2, 8, 12, 4, 7, 1, 15, 19, 20, 5, 16, 14, 18, 13] (by decide) (by decide)

def q213 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 12, 3, 10, 15, 0, 11, 7, 8, 6, 2, 9, 16, 4, 18, 13, 1, 5, 19, 14, 20]
    [5, 16, 10, 2, 13, 17, 9, 7, 8, 11, 3, 6, 1, 15, 19, 4, 12, 0, 14, 18, 20] (by decide) (by decide)

theorem c_10_12 : P 1369 (12 : Fin 21) :=
  ⟨1371, by decide, q212, q213, by decide +kernel, by decide +kernel⟩

def q214 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 13, 12, 4, 3, 5, 6, 17, 10, 9, 8, 18, 2, 1, 20, 16, 15, 7, 11, 19, 14]
    [0, 13, 12, 4, 3, 5, 6, 17, 10, 9, 8, 18, 2, 1, 20, 16, 15, 7, 11, 19, 14] (by decide) (by decide)

def q215 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 12, 11, 3, 10, 5, 13, 17, 9, 8, 4, 2, 1, 6, 16, 15, 14, 7, 18, 19, 0]
    [20, 12, 11, 3, 10, 5, 13, 17, 9, 8, 4, 2, 1, 6, 16, 15, 14, 7, 18, 19, 0] (by decide) (by decide)

theorem c_10_13 : P 1369 (13 : Fin 21) :=
  ⟨1371, by decide, q214, q215, by decide +kernel, by decide +kernel⟩

def q216 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 14, 18, 3, 4, 9, 6, 17, 10, 5, 8, 12, 11, 20, 1, 15, 16, 7, 2, 19, 13]
    [0, 14, 18, 3, 4, 9, 6, 17, 10, 5, 8, 12, 11, 20, 1, 15, 16, 7, 2, 19, 13] (by decide) (by decide)

def q217 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 14, 2, 3, 9, 5, 13, 17, 10, 4, 8, 11, 16, 6, 1, 15, 12, 7, 19, 18, 20]
    [0, 14, 2, 3, 9, 5, 13, 17, 10, 4, 8, 11, 16, 6, 1, 15, 12, 7, 19, 18, 20] (by decide) (by decide)

theorem c_10_14 : P 1369 (14 : Fin 21) :=
  ⟨1371, by decide, q216, q217, by decide +kernel, by decide +kernel⟩

def q218 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 15, 5, 4, 3, 2, 8, 19, 6, 11, 10, 9, 12, 14, 13, 1, 20, 17, 18, 7, 16]
    [0, 15, 5, 4, 3, 2, 8, 19, 6, 11, 10, 9, 12, 14, 13, 1, 20, 17, 18, 7, 16] (by decide) (by decide)

def q219 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 1, 4, 3, 2, 7, 15, 5, 11, 10, 9, 8, 19, 13, 18, 6, 16, 17, 14, 12, 0]
    [20, 1, 4, 3, 2, 7, 15, 5, 11, 10, 9, 8, 19, 13, 18, 6, 16, 17, 14, 12, 0] (by decide) (by decide)

theorem c_10_15 : P 1369 (15 : Fin 21) :=
  ⟨1371, by decide, q218, q219, by decide +kernel, by decide +kernel⟩

def q220 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 16, 9, 3, 4, 11, 8, 19, 6, 2, 10, 5, 18, 13, 14, 20, 1, 17, 12, 7, 15]
    [0, 16, 9, 3, 4, 11, 8, 19, 6, 2, 10, 5, 18, 13, 14, 20, 1, 17, 12, 7, 15] (by decide) (by decide)

def q221 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 16, 8, 3, 11, 7, 15, 5, 2, 9, 10, 4, 18, 13, 19, 6, 1, 17, 12, 14, 20]
    [0, 16, 8, 3, 11, 7, 15, 5, 2, 9, 10, 4, 18, 13, 19, 6, 1, 17, 12, 14, 20] (by decide) (by decide)

theorem c_10_16 : P 1369 (16 : Fin 21) :=
  ⟨1371, by decide, q220, q221, by decide +kernel, by decide +kernel⟩

def q222 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 17, 16, 3, 10, 9, 6, 14, 4, 19, 8, 1, 7, 15, 12, 20, 18, 11, 2, 5, 13]
    [0, 11, 18, 3, 8, 19, 6, 12, 10, 5, 4, 17, 14, 20, 7, 13, 2, 1, 16, 9, 15] (by decide) (by decide)

def q223 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 16, 2, 10, 9, 5, 13, 0, 3, 15, 8, 6, 14, 11, 19, 4, 18, 7, 1, 12, 20]
    [7, 18, 2, 8, 15, 5, 11, 17, 10, 4, 3, 13, 19, 6, 12, 9, 1, 0, 16, 14, 20] (by decide) (by decide)

theorem c_10_17 : P 1369 (17 : Fin 21) :=
  ⟨1371, by decide, q222, q223, by decide +kernel, by decide +kernel⟩

def q224 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 19, 3, 10, 1, 4, 5, 6, 16, 8, 9, 2, 15, 12, 13, 17, 11, 7, 14, 20]
    [0, 5, 12, 3, 6, 7, 8, 18, 10, 11, 4, 17, 14, 15, 19, 13, 9, 16, 1, 2, 20] (by decide) (by decide)

def q225 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 18, 3, 10, 6, 0, 4, 5, 2, 15, 8, 9, 1, 11, 12, 13, 16, 7, 14, 19, 20]
    [5, 12, 8, 2, 6, 7, 4, 17, 10, 11, 3, 13, 14, 15, 18, 9, 16, 0, 1, 19, 20] (by decide) (by decide)

theorem c_10_18 : P 1369 (18 : Fin 21) :=
  ⟨1371, by decide, q224, q225, by decide +kernel, by decide +kernel⟩

def q226 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 1, 3, 6, 11, 8, 16, 4, 7, 10, 14, 17, 20, 5, 13, 9, 18, 12, 2, 15]
    [0, 2, 19, 3, 8, 14, 4, 9, 6, 16, 10, 5, 18, 15, 11, 20, 7, 12, 17, 1, 13] (by decide) (by decide)

def q227 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 18, 8, 2, 11, 7, 15, 0, 3, 6, 10, 13, 16, 4, 12, 9, 14, 17, 19, 1, 20]
    [7, 19, 3, 8, 13, 0, 9, 5, 2, 15, 10, 4, 14, 11, 16, 6, 12, 17, 1, 18, 20] (by decide) (by decide)

theorem c_10_19 : P 1369 (19 : Fin 21) :=
  ⟨1371, by decide, q226, q227, by decide +kernel, by decide +kernel⟩

def q228 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 20, 11, 4, 3, 9, 6, 7, 8, 5, 10, 2, 18, 14, 13, 16, 15, 17, 12, 19, 1]
    [0, 20, 11, 4, 3, 9, 6, 7, 8, 5, 10, 2, 18, 14, 13, 16, 15, 17, 12, 19, 1] (by decide) (by decide)

def q229 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 16, 11, 3, 8, 5, 6, 7, 4, 10, 9, 2, 14, 13, 12, 15, 1, 17, 19, 18, 0]
    [20, 16, 11, 3, 8, 5, 6, 7, 4, 10, 9, 2, 14, 13, 12, 15, 1, 17, 19, 18, 0] (by decide) (by decide)

theorem c_10_20 : P 1369 (20 : Fin 21) :=
  ⟨1371, by decide, q228, q229, by decide +kernel, by decide +kernel⟩

theorem c_11_0 : P 1371 (0 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_11_1 : P 1371 (1 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_11_2 : P 1371 (2 : Fin 21) :=
  ⟨5501, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

theorem c_11_3 : P 1371 (3 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_11_4 : P 1371 (4 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q230 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 1, 8, 10, 13, 3, 16, 4, 20, 6, 14, 5, 7, 17, 11, 12, 19, 9, 15, 2]
    [0, 2, 20, 6, 8, 12, 10, 13, 3, 18, 4, 15, 16, 5, 11, 19, 7, 14, 1, 17, 9] (by decide) (by decide)

def q231 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 18, 8, 15, 9, 20, 2, 0, 4, 6, 13, 10, 12, 3, 16, 11, 19, 5, 14, 1, 7]
    [7, 19, 6, 13, 8, 17, 9, 20, 2, 4, 11, 15, 12, 10, 18, 3, 14, 0, 1, 16, 5] (by decide) (by decide)

theorem c_11_5 : P 1371 (5 : Fin 21) :=
  ⟨5501, by decide, q230, q231, by decide +kernel, by decide +kernel⟩

theorem c_11_6 : P 1371 (6 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q232 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 3, 1, 5, 7, 8, 15, 13, 11, 10, 20, 18, 14, 6, 4, 9, 17, 12, 2, 16]
    [0, 3, 19, 2, 15, 4, 14, 5, 6, 16, 10, 9, 18, 8, 13, 7, 20, 17, 12, 1, 11] (by decide) (by decide)

def q233 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 3, 8, 1, 12, 7, 15, 20, 18, 10, 6, 4, 14, 13, 11, 9, 16, 17, 19, 2, 0]
    [20, 3, 19, 1, 11, 0, 10, 5, 2, 15, 9, 14, 4, 13, 12, 6, 16, 17, 8, 18, 7] (by decide) (by decide)

theorem c_11_7 : P 1371 (7 : Fin 21) :=
  ⟨54781, by decide, q232, q233, by decide +kernel, by decide +kernel⟩

theorem c_11_8 : P 1371 (8 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q234 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 2, 10, 1, 11, 9, 6, 18, 17, 5, 3, 12, 15, 14, 8, 4, 7, 13, 20, 19, 16]
    [0, 3, 1, 10, 15, 9, 6, 16, 14, 5, 2, 4, 11, 17, 13, 12, 20, 8, 7, 19, 18] (by decide) (by decide)

def q235 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 9, 6, 18, 16, 5, 2, 17, 1, 10, 8, 11, 14, 13, 4, 3, 12, 20, 19, 15, 0]
    [20, 8, 6, 15, 14, 5, 2, 0, 10, 1, 9, 11, 16, 13, 12, 19, 4, 7, 3, 18, 17] (by decide) (by decide)

theorem c_11_9 : P 1371 (9 : Fin 21) :=
  ⟨54781, by decide, q234, q235, by decide +kernel, by decide +kernel⟩

theorem c_11_10 : P 1371 (10 : Fin 21) :=
  ⟨1371, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_11_11 : P 1371 (11 : Fin 21) :=
  ⟨5501, by decide, q226, q227, by decide +kernel, by decide +kernel⟩

def q236 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 5, 1, 10, 8, 2, 6, 19, 11, 3, 9, 13, 14, 12, 4, 17, 20, 15, 7, 16]
    [0, 3, 6, 10, 15, 2, 7, 19, 5, 11, 4, 9, 14, 12, 13, 18, 20, 16, 1, 8, 17] (by decide) (by decide)

def q237 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 4, 1, 6, 15, 7, 2, 5, 18, 10, 8, 9, 13, 19, 11, 3, 16, 20, 14, 12, 0]
    [20, 2, 6, 15, 1, 7, 3, 5, 10, 11, 9, 14, 19, 12, 18, 4, 16, 0, 8, 13, 17] (by decide) (by decide)

theorem c_11_12 : P 1371 (12 : Fin 21) :=
  ⟨54781, by decide, q236, q237, by decide +kernel, by decide +kernel⟩

theorem c_11_13 : P 1371 (13 : Fin 21) :=
  ⟨5501, by decide, q230, q231, by decide +kernel, by decide +kernel⟩

theorem c_11_14 : P 1371 (14 : Fin 21) :=
  ⟨54781, by decide, q60, q61, by decide +kernel, by decide +kernel⟩

def q238 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 11, 1, 6, 8, 18, 10, 14, 4, 12, 3, 16, 15, 9, 2, 19, 7, 13, 20, 17, 5]
    [0, 2, 14, 10, 8, 20, 3, 16, 4, 13, 6, 1, 9, 17, 7, 12, 11, 19, 5, 15, 18] (by decide) (by decide)

def q239 : Equiv.Perm (Fin 21) :=
  mkPerm [7, 18, 6, 13, 4, 17, 10, 0, 11, 8, 2, 15, 14, 9, 19, 3, 12, 20, 16, 1, 5]
    [7, 19, 10, 15, 4, 20, 2, 0, 9, 13, 6, 8, 16, 3, 12, 11, 18, 5, 1, 14, 17] (by decide) (by decide)

theorem c_11_15 : P 1371 (15 : Fin 21) :=
  ⟨5501, by decide, q238, q239, by decide +kernel, by decide +kernel⟩

theorem c_11_16 : P 1371 (16 : Fin 21) :=
  ⟨54781, by decide, q226, q227, by decide +kernel, by decide +kernel⟩

theorem c_11_17 : P 1371 (17 : Fin 21) :=
  ⟨5501, by decide, q226, q227, by decide +kernel, by decide +kernel⟩

theorem c_11_18 : P 1371 (18 : Fin 21) :=
  ⟨5501, by decide, q238, q239, by decide +kernel, by decide +kernel⟩

theorem c_11_19 : P 1371 (19 : Fin 21) :=
  ⟨5501, by decide, q70, q71, by decide +kernel, by decide +kernel⟩

def q240 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 13, 2, 1, 3, 10, 17, 8, 11, 18, 6, 7, 19, 16, 20, 4, 15, 9, 5, 12, 14]
    [0, 3, 2, 4, 15, 18, 10, 11, 7, 17, 5, 8, 19, 1, 20, 16, 13, 6, 9, 12, 14] (by decide) (by decide)

def q241 : Equiv.Perm (Fin 21) :=
  mkPerm [20, 9, 1, 8, 10, 17, 13, 7, 18, 2, 6, 3, 15, 16, 4, 11, 14, 5, 12, 19, 0]
    [20, 2, 9, 11, 14, 17, 10, 7, 3, 1, 4, 15, 18, 6, 16, 12, 13, 5, 8, 19, 0] (by decide) (by decide)

theorem c_11_20 : P 1371 (20 : Fin 21) :=
  ⟨54781, by decide, q240, q241, by decide +kernel, by decide +kernel⟩

theorem c_12_0 : P 6799 (0 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_1 : P 6799 (1 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_2 : P 6799 (2 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_3 : P 6799 (3 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q242 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 10, 2, 1, 18, 9, 5, 11, 7, 6, 3, 8, 20, 16, 12, 4, 17, 13, 15, 19, 14]
    [0, 3, 2, 10, 15, 6, 9, 8, 11, 5, 1, 7, 14, 17, 20, 18, 13, 16, 4, 19, 12] (by decide) (by decide)

def q243 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 9, 1, 18, 14, 5, 10, 7, 6, 2, 8, 4, 16, 12, 11, 3, 13, 20, 15, 19, 0]
    [20, 2, 9, 15, 11, 5, 8, 7, 10, 1, 6, 14, 13, 16, 4, 18, 12, 0, 3, 19, 17] (by decide) (by decide)

theorem c_12_4 : P 6799 (4 : Fin 21) :=
  ⟨54781, by decide, q242, q243, by decide +kernel, by decide +kernel⟩

theorem c_12_5 : P 6799 (5 : Fin 21) :=
  ⟨54781, by decide, q242, q243, by decide +kernel, by decide +kernel⟩

def q244 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 2, 1, 6, 12, 17, 7, 11, 18, 3, 8, 13, 16, 9, 14, 5, 20, 15, 10, 4]
    [0, 3, 2, 10, 20, 16, 4, 7, 11, 14, 19, 8, 5, 12, 15, 18, 13, 6, 9, 1, 17] (by decide) (by decide)

def q245 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 19, 1, 6, 11, 17, 3, 7, 18, 2, 8, 13, 12, 16, 14, 10, 4, 20, 15, 9, 0]
    [20, 2, 9, 6, 16, 0, 3, 7, 10, 19, 15, 4, 12, 11, 14, 18, 13, 5, 8, 1, 17] (by decide) (by decide)

theorem c_12_6 : P 6799 (6 : Fin 21) :=
  ⟨54781, by decide, q244, q245, by decide +kernel, by decide +kernel⟩

theorem c_12_7 : P 6799 (7 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_8 : P 6799 (8 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_9 : P 6799 (9 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q246 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 18, 2, 1, 10, 3, 15, 7, 11, 13, 9, 8, 19, 4, 12, 16, 17, 6, 5, 20, 14]
    [0, 3, 2, 5, 13, 18, 17, 7, 11, 10, 4, 8, 14, 9, 20, 6, 15, 16, 1, 12, 19] (by decide) (by decide)

def q247 : Equiv.Perm (Fin 21) :=
  mkPerm [17, 2, 1, 6, 10, 20, 14, 7, 18, 9, 8, 15, 3, 11, 12, 16, 13, 5, 4, 19, 0]
    [20, 2, 1, 12, 18, 17, 3, 7, 10, 9, 4, 13, 14, 16, 6, 11, 15, 0, 8, 19, 5] (by decide) (by decide)

theorem c_12_10 : P 6799 (10 : Fin 21) :=
  ⟨54781, by decide, q246, q247, by decide +kernel, by decide +kernel⟩

theorem c_12_11 : P 6799 (11 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_12 : P 6799 (12 : Fin 21) :=
  ⟨6799, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_12_13 : P 6799 (13 : Fin 21) :=
  ⟨54781, by decide, q244, q245, by decide +kernel, by decide +kernel⟩

theorem c_12_14 : P 6799 (14 : Fin 21) :=
  ⟨54781, by decide, q244, q245, by decide +kernel, by decide +kernel⟩

theorem c_12_15 : P 6799 (15 : Fin 21) :=
  ⟨54781, by decide, q246, q247, by decide +kernel, by decide +kernel⟩

theorem c_12_16 : P 6799 (16 : Fin 21) :=
  ⟨54781, by decide, q246, q247, by decide +kernel, by decide +kernel⟩

theorem c_12_17 : P 6799 (17 : Fin 21) :=
  ⟨54781, by decide, q244, q245, by decide +kernel, by decide +kernel⟩

theorem c_12_18 : P 6799 (18 : Fin 21) :=
  ⟨54781, by decide, q242, q243, by decide +kernel, by decide +kernel⟩

theorem c_12_19 : P 6799 (19 : Fin 21) :=
  ⟨54781, by decide, q246, q247, by decide +kernel, by decide +kernel⟩

theorem c_12_20 : P 6799 (20 : Fin 21) :=
  ⟨54781, by decide, q242, q243, by decide +kernel, by decide +kernel⟩

theorem c_13_0 : P 5501 (0 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_1 : P 5501 (1 : Fin 21) :=
  ⟨54781, by decide, q236, q237, by decide +kernel, by decide +kernel⟩

theorem c_13_2 : P 5501 (2 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_3 : P 5501 (3 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_4 : P 5501 (4 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_5 : P 5501 (5 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_6 : P 5501 (6 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_7 : P 5501 (7 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_8 : P 5501 (8 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_9 : P 5501 (9 : Fin 21) :=
  ⟨503803, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_13_10 : P 5501 (10 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_11 : P 5501 (11 : Fin 21) :=
  ⟨503803, by decide, q106, q107, by decide +kernel, by decide +kernel⟩

theorem c_13_12 : P 5501 (12 : Fin 21) :=
  ⟨5501, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_13 : P 5501 (13 : Fin 21) :=
  ⟨54781, by decide, q236, q237, by decide +kernel, by decide +kernel⟩

theorem c_13_14 : P 5501 (14 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_13_15 : P 5501 (15 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

def q248 : Equiv.Perm (Fin 21) :=
  mkPerm [0, 19, 10, 2, 5, 16, 4, 17, 12, 14, 3, 18, 20, 11, 6, 8, 9, 15, 13, 1, 7]
    [0, 19, 3, 10, 6, 4, 14, 20, 15, 16, 2, 13, 8, 18, 9, 17, 5, 7, 11, 1, 12] (by decide) (by decide)

def q249 : Equiv.Perm (Fin 21) :=
  mkPerm [5, 15, 9, 1, 12, 0, 3, 17, 19, 10, 2, 4, 16, 11, 13, 8, 14, 20, 18, 6, 7]
    [5, 3, 10, 6, 11, 0, 19, 20, 15, 2, 9, 13, 4, 14, 16, 1, 12, 7, 18, 8, 17] (by decide) (by decide)

theorem c_13_16 : P 5501 (16 : Fin 21) :=
  ⟨54781, by decide, q248, q249, by decide +kernel, by decide +kernel⟩

theorem c_13_17 : P 5501 (17 : Fin 21) :=
  ⟨54781, by decide, q248, q249, by decide +kernel, by decide +kernel⟩

theorem c_13_18 : P 5501 (18 : Fin 21) :=
  ⟨503803, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_13_19 : P 5501 (19 : Fin 21) :=
  ⟨54781, by decide, q236, q237, by decide +kernel, by decide +kernel⟩

theorem c_13_20 : P 5501 (20 : Fin 21) :=
  ⟨54781, by decide, q248, q249, by decide +kernel, by decide +kernel⟩

theorem c_14_0 : P 54781 (0 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_1 : P 54781 (1 : Fin 21) :=
  ⟨503803, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_14_2 : P 54781 (2 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_3 : P 54781 (3 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_4 : P 54781 (4 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_5 : P 54781 (5 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_6 : P 54781 (6 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_7 : P 54781 (7 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_8 : P 54781 (8 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_9 : P 54781 (9 : Fin 21) :=
  ⟨503803, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_14_10 : P 54781 (10 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_11 : P 54781 (11 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_12 : P 54781 (12 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_13 : P 54781 (13 : Fin 21) :=
  ⟨503803, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_14_14 : P 54781 (14 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_15 : P 54781 (15 : Fin 21) :=
  ⟨54781, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_14_16 : P 54781 (16 : Fin 21) :=
  ⟨503803, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_14_17 : P 54781 (17 : Fin 21) :=
  ⟨503803, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_14_18 : P 54781 (18 : Fin 21) :=
  ⟨503803, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_14_19 : P 54781 (19 : Fin 21) :=
  ⟨503803, by decide, q110, q111, by decide +kernel, by decide +kernel⟩

theorem c_14_20 : P 54781 (20 : Fin 21) :=
  ⟨503803, by decide, q40, q41, by decide +kernel, by decide +kernel⟩

theorem c_15_0 : P 503803 (0 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_1 : P 503803 (1 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_2 : P 503803 (2 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_3 : P 503803 (3 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_4 : P 503803 (4 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_5 : P 503803 (5 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_6 : P 503803 (6 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_7 : P 503803 (7 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_8 : P 503803 (8 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_9 : P 503803 (9 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_10 : P 503803 (10 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_11 : P 503803 (11 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_12 : P 503803 (12 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_13 : P 503803 (13 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_14 : P 503803 (14 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_15 : P 503803 (15 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_16 : P 503803 (16 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_17 : P 503803 (17 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_18 : P 503803 (18 : Fin 21) :=
  ⟨503803, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_19 : P 503803 (19 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_15_20 : P 503803 (20 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_0 : P 2097151 (0 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_1 : P 2097151 (1 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_2 : P 2097151 (2 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_3 : P 2097151 (3 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_4 : P 2097151 (4 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_5 : P 2097151 (5 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_6 : P 2097151 (6 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_7 : P 2097151 (7 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_8 : P 2097151 (8 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_9 : P 2097151 (9 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_10 : P 2097151 (10 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_11 : P 2097151 (11 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_12 : P 2097151 (12 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_13 : P 2097151 (13 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_14 : P 2097151 (14 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_15 : P 2097151 (15 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_16 : P 2097151 (16 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_17 : P 2097151 (17 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_18 : P 2097151 (18 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_19 : P 2097151 (19 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem c_16_20 : P 2097151 (20 : Fin 21) :=
  ⟨2097151, by decide, q0, q0, by decide +kernel, by decide +kernel⟩

theorem m_0 : ∀ x7 : Fin 21, P 0 x7 := by
  intro x7
  fin_cases x7
  · exact c_0_0
  · exact c_0_1
  · exact c_0_2
  · exact c_0_3
  · exact c_0_4
  · exact c_0_5
  · exact c_0_6
  · exact c_0_7
  · exact c_0_8
  · exact c_0_9
  · exact c_0_10
  · exact c_0_11
  · exact c_0_12
  · exact c_0_13
  · exact c_0_14
  · exact c_0_15
  · exact c_0_16
  · exact c_0_17
  · exact c_0_18
  · exact c_0_19
  · exact c_0_20

theorem m_1 : ∀ x7 : Fin 21, P 1 x7 := by
  intro x7
  fin_cases x7
  · exact c_1_0
  · exact c_1_1
  · exact c_1_2
  · exact c_1_3
  · exact c_1_4
  · exact c_1_5
  · exact c_1_6
  · exact c_1_7
  · exact c_1_8
  · exact c_1_9
  · exact c_1_10
  · exact c_1_11
  · exact c_1_12
  · exact c_1_13
  · exact c_1_14
  · exact c_1_15
  · exact c_1_16
  · exact c_1_17
  · exact c_1_18
  · exact c_1_19
  · exact c_1_20

theorem m_2 : ∀ x7 : Fin 21, P 3 x7 := by
  intro x7
  fin_cases x7
  · exact c_2_0
  · exact c_2_1
  · exact c_2_2
  · exact c_2_3
  · exact c_2_4
  · exact c_2_5
  · exact c_2_6
  · exact c_2_7
  · exact c_2_8
  · exact c_2_9
  · exact c_2_10
  · exact c_2_11
  · exact c_2_12
  · exact c_2_13
  · exact c_2_14
  · exact c_2_15
  · exact c_2_16
  · exact c_2_17
  · exact c_2_18
  · exact c_2_19
  · exact c_2_20

theorem m_3 : ∀ x7 : Fin 21, P 19 x7 := by
  intro x7
  fin_cases x7
  · exact c_3_0
  · exact c_3_1
  · exact c_3_2
  · exact c_3_3
  · exact c_3_4
  · exact c_3_5
  · exact c_3_6
  · exact c_3_7
  · exact c_3_8
  · exact c_3_9
  · exact c_3_10
  · exact c_3_11
  · exact c_3_12
  · exact c_3_13
  · exact c_3_14
  · exact c_3_15
  · exact c_3_16
  · exact c_3_17
  · exact c_3_18
  · exact c_3_19
  · exact c_3_20

theorem m_4 : ∀ x7 : Fin 21, P 7 x7 := by
  intro x7
  fin_cases x7
  · exact c_4_0
  · exact c_4_1
  · exact c_4_2
  · exact c_4_3
  · exact c_4_4
  · exact c_4_5
  · exact c_4_6
  · exact c_4_7
  · exact c_4_8
  · exact c_4_9
  · exact c_4_10
  · exact c_4_11
  · exact c_4_12
  · exact c_4_13
  · exact c_4_14
  · exact c_4_15
  · exact c_4_16
  · exact c_4_17
  · exact c_4_18
  · exact c_4_19
  · exact c_4_20

theorem m_5 : ∀ x7 : Fin 21, P 389 x7 := by
  intro x7
  fin_cases x7
  · exact c_5_0
  · exact c_5_1
  · exact c_5_2
  · exact c_5_3
  · exact c_5_4
  · exact c_5_5
  · exact c_5_6
  · exact c_5_7
  · exact c_5_8
  · exact c_5_9
  · exact c_5_10
  · exact c_5_11
  · exact c_5_12
  · exact c_5_13
  · exact c_5_14
  · exact c_5_15
  · exact c_5_16
  · exact c_5_17
  · exact c_5_18
  · exact c_5_19
  · exact c_5_20

theorem m_6 : ∀ x7 : Fin 21, P 23 x7 := by
  intro x7
  fin_cases x7
  · exact c_6_0
  · exact c_6_1
  · exact c_6_2
  · exact c_6_3
  · exact c_6_4
  · exact c_6_5
  · exact c_6_6
  · exact c_6_7
  · exact c_6_8
  · exact c_6_9
  · exact c_6_10
  · exact c_6_11
  · exact c_6_12
  · exact c_6_13
  · exact c_6_14
  · exact c_6_15
  · exact c_6_16
  · exact c_6_17
  · exact c_6_18
  · exact c_6_19
  · exact c_6_20

theorem m_7 : ∀ x7 : Fin 21, P 15 x7 := by
  intro x7
  fin_cases x7
  · exact c_7_0
  · exact c_7_1
  · exact c_7_2
  · exact c_7_3
  · exact c_7_4
  · exact c_7_5
  · exact c_7_6
  · exact c_7_7
  · exact c_7_8
  · exact c_7_9
  · exact c_7_10
  · exact c_7_11
  · exact c_7_12
  · exact c_7_13
  · exact c_7_14
  · exact c_7_15
  · exact c_7_16
  · exact c_7_17
  · exact c_7_18
  · exact c_7_19
  · exact c_7_20

theorem m_8 : ∀ x7 : Fin 21, P 31 x7 := by
  intro x7
  fin_cases x7
  · exact c_8_0
  · exact c_8_1
  · exact c_8_2
  · exact c_8_3
  · exact c_8_4
  · exact c_8_5
  · exact c_8_6
  · exact c_8_7
  · exact c_8_8
  · exact c_8_9
  · exact c_8_10
  · exact c_8_11
  · exact c_8_12
  · exact c_8_13
  · exact c_8_14
  · exact c_8_15
  · exact c_8_16
  · exact c_8_17
  · exact c_8_18
  · exact c_8_19
  · exact c_8_20

theorem m_9 : ∀ x7 : Fin 21, P 95 x7 := by
  intro x7
  fin_cases x7
  · exact c_9_0
  · exact c_9_1
  · exact c_9_2
  · exact c_9_3
  · exact c_9_4
  · exact c_9_5
  · exact c_9_6
  · exact c_9_7
  · exact c_9_8
  · exact c_9_9
  · exact c_9_10
  · exact c_9_11
  · exact c_9_12
  · exact c_9_13
  · exact c_9_14
  · exact c_9_15
  · exact c_9_16
  · exact c_9_17
  · exact c_9_18
  · exact c_9_19
  · exact c_9_20

theorem m_10 : ∀ x7 : Fin 21, P 1369 x7 := by
  intro x7
  fin_cases x7
  · exact c_10_0
  · exact c_10_1
  · exact c_10_2
  · exact c_10_3
  · exact c_10_4
  · exact c_10_5
  · exact c_10_6
  · exact c_10_7
  · exact c_10_8
  · exact c_10_9
  · exact c_10_10
  · exact c_10_11
  · exact c_10_12
  · exact c_10_13
  · exact c_10_14
  · exact c_10_15
  · exact c_10_16
  · exact c_10_17
  · exact c_10_18
  · exact c_10_19
  · exact c_10_20

theorem m_11 : ∀ x7 : Fin 21, P 1371 x7 := by
  intro x7
  fin_cases x7
  · exact c_11_0
  · exact c_11_1
  · exact c_11_2
  · exact c_11_3
  · exact c_11_4
  · exact c_11_5
  · exact c_11_6
  · exact c_11_7
  · exact c_11_8
  · exact c_11_9
  · exact c_11_10
  · exact c_11_11
  · exact c_11_12
  · exact c_11_13
  · exact c_11_14
  · exact c_11_15
  · exact c_11_16
  · exact c_11_17
  · exact c_11_18
  · exact c_11_19
  · exact c_11_20

theorem m_12 : ∀ x7 : Fin 21, P 6799 x7 := by
  intro x7
  fin_cases x7
  · exact c_12_0
  · exact c_12_1
  · exact c_12_2
  · exact c_12_3
  · exact c_12_4
  · exact c_12_5
  · exact c_12_6
  · exact c_12_7
  · exact c_12_8
  · exact c_12_9
  · exact c_12_10
  · exact c_12_11
  · exact c_12_12
  · exact c_12_13
  · exact c_12_14
  · exact c_12_15
  · exact c_12_16
  · exact c_12_17
  · exact c_12_18
  · exact c_12_19
  · exact c_12_20

theorem m_13 : ∀ x7 : Fin 21, P 5501 x7 := by
  intro x7
  fin_cases x7
  · exact c_13_0
  · exact c_13_1
  · exact c_13_2
  · exact c_13_3
  · exact c_13_4
  · exact c_13_5
  · exact c_13_6
  · exact c_13_7
  · exact c_13_8
  · exact c_13_9
  · exact c_13_10
  · exact c_13_11
  · exact c_13_12
  · exact c_13_13
  · exact c_13_14
  · exact c_13_15
  · exact c_13_16
  · exact c_13_17
  · exact c_13_18
  · exact c_13_19
  · exact c_13_20

theorem m_14 : ∀ x7 : Fin 21, P 54781 x7 := by
  intro x7
  fin_cases x7
  · exact c_14_0
  · exact c_14_1
  · exact c_14_2
  · exact c_14_3
  · exact c_14_4
  · exact c_14_5
  · exact c_14_6
  · exact c_14_7
  · exact c_14_8
  · exact c_14_9
  · exact c_14_10
  · exact c_14_11
  · exact c_14_12
  · exact c_14_13
  · exact c_14_14
  · exact c_14_15
  · exact c_14_16
  · exact c_14_17
  · exact c_14_18
  · exact c_14_19
  · exact c_14_20

theorem m_15 : ∀ x7 : Fin 21, P 503803 x7 := by
  intro x7
  fin_cases x7
  · exact c_15_0
  · exact c_15_1
  · exact c_15_2
  · exact c_15_3
  · exact c_15_4
  · exact c_15_5
  · exact c_15_6
  · exact c_15_7
  · exact c_15_8
  · exact c_15_9
  · exact c_15_10
  · exact c_15_11
  · exact c_15_12
  · exact c_15_13
  · exact c_15_14
  · exact c_15_15
  · exact c_15_16
  · exact c_15_17
  · exact c_15_18
  · exact c_15_19
  · exact c_15_20

theorem m_16 : ∀ x7 : Fin 21, P 2097151 x7 := by
  intro x7
  fin_cases x7
  · exact c_16_0
  · exact c_16_1
  · exact c_16_2
  · exact c_16_3
  · exact c_16_4
  · exact c_16_5
  · exact c_16_6
  · exact c_16_7
  · exact c_16_8
  · exact c_16_9
  · exact c_16_10
  · exact c_16_11
  · exact c_16_12
  · exact c_16_13
  · exact c_16_14
  · exact c_16_15
  · exact c_16_16
  · exact c_16_17
  · exact c_16_18
  · exact c_16_19
  · exact c_16_20

theorem main : ∀ x5 ∈ ([0, 1, 3, 19, 7, 389, 23, 15, 31, 95, 1369, 1371, 6799, 5501, 54781, 503803, 2097151] : List ℕ), ∀ x7 : Fin 21, P x5 x7 := by
  intro x5 hx5 x7
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx5
  rcases hx5 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m_0 x7
  · exact m_1 x7
  · exact m_2 x7
  · exact m_3 x7
  · exact m_4 x7
  · exact m_5 x7
  · exact m_6 x7
  · exact m_7 x7
  · exact m_8 x7
  · exact m_9 x7
  · exact m_10 x7
  · exact m_11 x7
  · exact m_12 x7
  · exact m_13 x7
  · exact m_14 x7
  · exact m_15 x7
  · exact m_16 x7

end PEqualNP.Outside.L_meta_7099

theorem PEqualNP.Outside.L_meta_7099 : let x1 : Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x1 x2 : Fin (21 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (21 : ℕ)) ∨ x1 = x2 + (4 : Fin (21 : ℕ)) ∨ x1 = x2 + (14 : Fin (21 : ℕ)) ∨ x1 = x2 + (16 : Fin (21 : ℕ)); have x2 : Finset (Fin (21 : ℕ)) → Finset (Fin (21 : ℕ)) := fun (x2 : Finset (Fin (21 : ℕ))) => {x3 : Fin (21 : ℕ) | ∀ (x4 : Fin (21 : ℕ)), (∀ x5 ∈ x2, ¬x1 x5 x4) → ¬x1 x3 x4}; have x3 : ℕ → Finset (Fin (21 : ℕ)) := fun (x3 : ℕ) => {x4 : Fin (21 : ℕ) | x3.testBit ↑x4 = Bool.true}; have x4 : List ℕ := [(0 : ℕ), (1 : ℕ), (3 : ℕ), (19 : ℕ), (7 : ℕ), (389 : ℕ), (23 : ℕ), (15 : ℕ), (31 : ℕ), (95 : ℕ), (1369 : ℕ), (1371 : ℕ), (6799 : ℕ), (5501 : ℕ), (54781 : ℕ), (503803 : ℕ), (2097151 : ℕ)]; ∀ x5 ∈ x4, ∀ (x7 : Fin (21 : ℕ)), ∃ x8 ∈ x4, ∃ (x9 : Equiv.Perm (Fin (21 : ℕ))) (x10 : Equiv.Perm (Fin (21 : ℕ))), (∀ (x11 x12 : Fin (21 : ℕ)), x1 (x9 x11) (x10 x12) ↔ x1 x11 x12) ∧ x2 (Insert.insert x7 (x3 x5)) = Finset.map (Equiv.toEmbedding x9) (x3 x8) := by
  exact PEqualNP.Outside.L_meta_7099.main
