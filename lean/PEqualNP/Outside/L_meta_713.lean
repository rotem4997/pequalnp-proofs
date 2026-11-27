import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  intro n m r S B degree
  classical
  let hits (T : Finset (Fin n)) := Finset.univ.filter (fun i => ∃ p ∈ T, p ∈ S i)
  change (hits B).card ≤ B.card * r
  induction B using Finset.induction_on with
  | empty => simp [hits]
  | @insert p B hp ih =>
    let I := Finset.univ.filter (fun i => p ∈ S i)
    have union_eq : hits (insert p B) = I ∪ hits B := by
      ext i
      simp [hits, I]
    rw [union_eq, Finset.card_insert_of_notMem hp, Nat.add_mul, one_mul]
    have hI : I.card ≤ r := degree p
    have hu := Finset.card_union_le I (hits B)
    omega
