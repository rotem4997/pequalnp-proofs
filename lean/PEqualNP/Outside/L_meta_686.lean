import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_686
end PEqualNP.Outside.L_meta_686

open PEqualNP.Outside.L_meta_686 in
theorem PEqualNP.Outside.L_meta_686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  intro m n r S hp hr B
  classical
  let T := fun A : Finset (Fin n) => Finset.univ.filter (fun i : Fin m => ∃ x ∈ A, x ∈ S i)
  change (T B).card + B.card ≤ B.card * r + 1
  induction B using Finset.induction_on with
  | empty => simp [T]
  | @insert a B ha ih =>
    let U := Finset.univ.filter (fun i : Fin m => a ∈ S i)
    have he : T (insert a B) = U ∪ T B := by
      ext i
      simp [T, U]
    rw [he, Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul]
    have hu : U.card = r := hr a
    by_cases hB : B.Nonempty
    · obtain ⟨b, hb⟩ := hB
      have hab : a ≠ b := fun e => ha (e ▸ hb)
      obtain ⟨i, hi, hj⟩ := hp a b hab
      have hI : 0 < (U ∩ T B).card := Finset.card_pos.mpr ⟨i,
        Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, hj⟩⟩⟩
      have hc := Finset.card_union_add_card_inter U (T B)
      omega
    · have hE := Finset.not_nonempty_iff_eq_empty.mp hB
      subst B
      simp [T, hu]
