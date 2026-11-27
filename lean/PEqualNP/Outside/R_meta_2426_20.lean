import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2426_20
    (mono :
      ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
        (∀ i, x i = true → y i = true) →
        circuitFun n C x = true → circuitFun n C y = true)
    (search :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let edges (p l : Fin 13) := ∃ d ∈ diff, p = l + d
      let pins : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25], [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24], [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
      let f (C : Circuit) (x : Fin 26 → Bool) :=
        circuitFun 26 C (fun i => (pins.getD i.val []).any (fun j => x (Fin.ofNat 26 j)))
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 13 ∧
        (∀ p l : Fin 13, p.val < 3 → edges p l →
          f C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
        (∀ A : Finset (Fin 3),
          f C (fun i => Fin.addCases (motive := fun _ => Bool)
            (fun p : Fin 13 => decide (3 ≤ p.val ∨ ∃ a ∈ A, Fin.castAdd 10 a = p))
            (fun l : Fin 13 => decide (∀ a ∈ A, ¬ edges (Fin.castAdd 10 a) l)) i) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (List ℕ) := [[(0 : ℕ)], [(1 : ℕ)], [(2 : ℕ)], [(13 : ℕ)], [(14 : ℕ)], [(15 : ℕ)], [(17 : ℕ)], [(18 : ℕ)], [(19 : ℕ)], [(23 : ℕ)], [(24 : ℕ)], [(25 : ℕ)], [(13 : ℕ), (15 : ℕ)], [(14 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ)], [(15 : ℕ), (17 : ℕ), (18 : ℕ)], [(19 : ℕ), (23 : ℕ)], [(18 : ℕ), (19 : ℕ), (23 : ℕ)], [(17 : ℕ), (24 : ℕ)], [(17 : ℕ), (19 : ℕ), (24 : ℕ)], [(18 : ℕ), (25 : ℕ)], [(13 : ℕ), (19 : ℕ)], [(14 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ)], [(15 : ℕ), (23 : ℕ), (24 : ℕ)], [(24 : ℕ), (25 : ℕ)]]; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size ≤ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x3 fun (x5 : Fin (26 : ℕ)) => (x2.getD ↑x5 []).any fun (x6 : ℕ) => x4 (Fin.ofNat (26 : ℕ) x6)) = Decidable.decide (∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), ↑x5 < (3 : ℕ) ∧ (∃ x7 ∈ x1, x5 = x6 + x7) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) := by
  classical
  let diff : Finset (Fin 13) := {0, 1, 3, 9}
  let edges (p l : Fin 13) := ∃ d ∈ diff, p = l + d
  let pins : List (List ℕ) := [[0], [1], [2], [13], [14], [15], [17], [18], [19], [23], [24], [25], [13, 15], [14, 17], [15, 17], [15, 17, 18], [19, 23], [18, 19, 23], [17, 24], [17, 19, 24], [18, 25], [13, 19], [14, 23], [15, 23], [15, 23, 24], [24, 25]]
  let f (C : Circuit) (x : Fin 26 → Bool) :=
    circuitFun 26 C (fun i => (pins.getD i.val []).any (fun j => x (Fin.ofNat 26 j)))
  obtain ⟨C, hC, hSize, pos, neg⟩ := search
  refine ⟨C, hC, hSize, ?_⟩
  have hMono (x y : Fin 26 → Bool) (h : ∀ i, x i = true → y i = true) :
      f C x = true → f C y = true := by
    apply mono 26 C hC
    intro i hi
    obtain ⟨j, hmem, hbit⟩ := List.any_eq_true.mp hi
    exact List.any_eq_true.mpr ⟨j, hmem, h _ hbit⟩
  intro x
  change f C x = decide (∃ p l : Fin 13, p.val < 3 ∧ edges p l ∧
    x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro accept
    by_contra hbad
    let A : Finset (Fin 3) := Finset.univ.filter
      (fun a => x (Fin.castAdd 13 (Fin.castAdd 10 a)) = true)
    let y : Fin 26 → Bool := fun i => Fin.addCases (motive := fun _ => Bool)
      (fun p : Fin 13 => decide (3 ≤ p.val ∨ ∃ a ∈ A, Fin.castAdd 10 a = p))
      (fun l : Fin 13 => decide (∀ a ∈ A, ¬ edges (Fin.castAdd 10 a) l)) i
    have dominates (i : Fin (13 + 13)) : x i = true → y i = true := by
      induction i using Fin.addCases with
      | left p =>
        intro on
        simp only [y, Fin.addCases_left, decide_eq_true_eq]
        by_cases hsmall : p.val < 3
        · let a : Fin 3 := ⟨p.val, hsmall⟩
          have hp : Fin.castAdd 10 a = p := Fin.ext rfl
          refine Or.inr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hp⟩
          simpa only [hp] using on
        · exact Or.inl (by omega)
      | right l =>
        intro on
        simp only [y, Fin.addCases_right, decide_eq_true_eq]
        intro a ha hij
        have hp := (Finset.mem_filter.mp ha).2
        exact hbad ⟨Fin.castAdd 10 a, l, a.isLt, hij, hp, on⟩
    have reject : f C y = false := neg A
    exact Bool.noConfusion ((hMono x y dominates accept).symm.trans reject)
  · rintro ⟨p, l, hp, edge, honP, honL⟩
    let y (i : Fin 26) : Bool := decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    apply hMono y x _ (pos p l hp edge)
    intro i hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact honP
    · exact honL
