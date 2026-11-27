import Mathlib
import PEqualNP.Defs

-- Represent each available signal by either polarity of an earlier wire.
-- An OR becomes the complement of an AND by De Morgan's law.
-- The two specified negations then need no new binary gates.
theorem PEqualNP.Outside.R_meta_2547_1
    (normalize : ∀ (α : Type) (base source : List (α → Bool)),
    let pool := fun i : Fin source.length => base ++ source.take i.val
    let neg := fun i : Fin source.length => ∃ f ∈ pool i, source.get i = fun x => !f x
    let signs := fun L : List (α → Bool) => L ++ L.map (fun f x => !f x)
    (∀ i, ∃ f ∈ pool i, ∃ g ∈ pool i,
      (source.get i = fun x => f x && g x) ∨ (source.get i = fun x => f x || g x) ∨
        source.get i = fun x => !f x) →
    (∃ i j, i < j ∧ neg i ∧ neg j) →
    ∃ gates : List (α → Bool), gates.length + 2 ≤ source.length ∧
      (∀ k : Fin gates.length, let P := signs (base ++ gates.take k.val)
        ∃ f ∈ P, ∃ g ∈ P, gates.get k = fun x => f x && g x) ∧
      ∀ f ∈ base ++ source, f ∈ signs (base ++ gates))
    (lower : let base : List ((Fin 9 → Bool) → Bool) := (fun _ => false) :: (fun _ => true) :: ((List.ofFn (fun i : Fin 9 => fun x : Fin 9 → Bool => x i)) ++
      [fun x : Fin 9 → Bool => x 0 && x 4])
    let signs := fun L : List ((Fin 9 → Bool) → Bool) => L ++ L.map (fun f x => !f x)
    ∀ gates : List ((Fin 9 → Bool) → Bool),
      (∀ k : Fin gates.length, let P := signs (base ++ gates.take k.val)
        ∃ f ∈ P, ∃ g ∈ P, gates.get k = fun x => f x && g x) →
      (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ∈ signs (base ++ gates) → 13 ≤ gates.length) :
    have x1 : List ((Fin (9 : ℕ) → Bool) → Bool) := (List.ofFn fun (x1 : Fin (9 : ℕ)) (x2 : Fin (9 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ))]; ∀ (x2 : List ((Fin (9 : ℕ) → Bool) → Bool)),   (∀ (x3 : Fin x2.length),       have x4 : List ((Fin (9 : ℕ) → Bool) → Bool) := (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x4 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x1 ++ List.take (↑x3) x2);       ∃ x5 ∈ x4, ∃ x6 ∈ x4, (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 && x6 x7) ∨ (x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => x5 x7 || x6 x7) ∨ x2.get x3 = fun (x7 : Fin (9 : ℕ) → Bool) => !x5 x7) →     (∃ (x4 : Fin x2.length) (x5 : Fin x2.length), x4 < x5 ∧ (∃ x6 ∈ (fun (x7 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x7 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x1 ++ List.take (↑x4) x2), x2.get x4 = fun (x7 : Fin (9 : ℕ) → Bool) => !x6 x7) ∧ ∃ x6 ∈ (fun (x7 : Fin (9 : ℕ) → Bool) => Bool.false) :: (fun (x7 : Fin (9 : ℕ) → Bool) => Bool.true) :: (x1 ++ List.take (↑x5) x2), x2.get x5 = fun (x7 : Fin (9 : ℕ) → Bool) => !x6 x7) → (fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) ∈ (fun (x5 : Fin (9 : ℕ) → Bool) => Bool.false) :: (x1 ++ x2) → (15 : ℕ) ≤ x2.length := by
  let initial : List ((Fin 9 → Bool) → Bool) := (List.ofFn (fun i : Fin 9 => fun x : Fin 9 → Bool => x i)) ++
      [fun x : Fin 9 → Bool => x 0 && x 4]
  let base : List ((Fin 9 → Bool) → Bool) := (fun _ => false) :: (fun _ => true) :: initial
  intro postedSeed source legal negs output
  obtain ⟨gates, saved, circuit, keeps⟩ := normalize (Fin 9 → Bool) base source legal negs
  apply Nat.le_trans (show 15 = 13 + 2 by decide).le
  apply (Nat.add_le_add_right (lower gates circuit ?_) 2).trans saved
  apply keeps
  change (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ∈ (fun _ => false) :: (initial ++ source) at output
  change (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ∈ (fun _ => false) :: (fun _ => true) :: (initial ++ source)
  rcases List.mem_cons.mp output with h | h
  · exact List.mem_cons.mpr (Or.inl h)
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
