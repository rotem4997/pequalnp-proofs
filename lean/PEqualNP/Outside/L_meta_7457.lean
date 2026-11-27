import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7457_aux

theorem pre {α β : Type} (g : List α → β → α) : ∀ (ds : List β) (acc : List α),
    ∃ t, List.foldl (fun a d => a ++ [g a d]) acc ds = acc ++ t := by
  intro ds
  induction ds with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons d ds ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (acc ++ [g acc d])
    exact ⟨[g acc d] ++ t, by simp [List.foldl_cons, ht]⟩

theorem enc (x1 : List (BitVec 59)) : ∀ x2 : List (BitVec 59), x1.length + x2.length ≤ 40 →
    (∀ (x5 : Fin x2.length), ∃ x6 ∈ x1 ++ List.take (↑x5) x2, ∃ x7 ∈ x1 ++ List.take (↑x5) x2,
      x2.get x5 = x6 &&& x7 ∨ x2.get x5 = x6 ||| x7) →
    ∃ ds : List (Bool × Fin 40 × Fin 40), ds.length = x2.length ∧
      List.foldl (fun (x8 : List (BitVec 59)) (x9 : Bool × Fin 40 × Fin 40) =>
        x8 ++ [if x9.1 = Bool.true then x8.getD ↑x9.2.1 (0 : BitVec 59) ||| x8.getD ↑x9.2.2 (0 : BitVec 59)
          else x8.getD ↑x9.2.1 (0 : BitVec 59) &&& x8.getD ↑x9.2.2 (0 : BitVec 59)]) x1 ds = x1 ++ x2 := by
  intro x2
  induction x2 using List.reverseRecOn with
  | nil => intro _ _; exact ⟨[], rfl, by simp⟩
  | append_singleton l a ih =>
    intro hlen h
    have hl : x1.length + l.length < 40 := by
      simp at hlen
      omega
    obtain ⟨ds, hds, hf⟩ := ih (by omega) (by
      intro x5
      have h5 := h ⟨x5.1, by simp⟩
      have e1 : List.take x5.1 (l ++ [a]) = List.take x5.1 l :=
        List.take_append_of_le_length (Nat.le_of_lt x5.2)
      have e2 : (l ++ [a]).get ⟨x5.1, by simp⟩ = l.get x5 := by
        simp [List.getElem_append_left x5.2]
      simp only [e1] at h5
      rw [e2] at h5
      exact h5)
    obtain ⟨u, hu, v, hv, huv⟩ := h ⟨l.length, by simp⟩
    have ht : List.take l.length (l ++ [a]) = l := by simp
    have hg : (l ++ [a]).get ⟨l.length, by simp⟩ = a := by simp
    simp only [ht] at hu hv
    rw [hg] at huv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi2 : i < 40 := by
      simp at hi
      omega
    have hj2 : j < 40 := by
      simp at hj
      omega
    rcases huv with huv | huv
    · refine ⟨ds ++ [(Bool.false, ⟨i, hi2⟩, ⟨j, hj2⟩)], by simp [hds], ?_⟩
      rw [List.foldl_append, hf, huv]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    · refine ⟨ds ++ [(Bool.true, ⟨i, hi2⟩, ⟨j, hj2⟩)], by simp [hds], ?_⟩
      rw [List.foldl_append, hf, huv]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]

end PEqualNP.Outside.L_meta_7457_aux

theorem PEqualNP.Outside.L_meta_7457 : ∀ (x1 x2 : List (BitVec (59 : ℕ))), x1.length = (14 : ℕ) → x2.length ≤ (25 : ℕ) → (∀ (x5 : Fin x2.length), ∃ x6 ∈ x1 ++ List.take (↑x5) x2, ∃ x7 ∈ x1 ++ List.take (↑x5) x2, x2.get x5 = x6 &&& x7 ∨ x2.get x5 = x6 ||| x7) → ∃ (x6 : List (Bool × Fin (40 : ℕ) × Fin (40 : ℕ))), x6.length = (25 : ℕ) ∧ ∀ (x7 : Fin x2.length), (List.foldl (fun (x8 : List (BitVec (59 : ℕ))) (x9 : Bool × Fin (40 : ℕ) × Fin (40 : ℕ)) => x8 ++ [if x9.1 = Bool.true then x8.getD ↑x9.2.1 (0 : BitVec (59 : ℕ)) ||| x8.getD ↑x9.2.2 (0 : BitVec (59 : ℕ)) else x8.getD ↑x9.2.1 (0 : BitVec (59 : ℕ)) &&& x8.getD ↑x9.2.2 (0 : BitVec (59 : ℕ))]) x1 x6).getD ((14 : ℕ) + ↑x7) (0 : BitVec (59 : ℕ)) = x2.get x7 := by
  intro x1 x2 h1 h2 h
  obtain ⟨ds, hds, hf⟩ := PEqualNP.Outside.L_meta_7457_aux.enc x1 x2 (by omega) h
  obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_7457_aux.pre
    (fun (x8 : List (BitVec 59)) (x9 : Bool × Fin 40 × Fin 40) =>
      if x9.1 = Bool.true then x8.getD ↑x9.2.1 (0 : BitVec 59) ||| x8.getD ↑x9.2.2 (0 : BitVec 59)
        else x8.getD ↑x9.2.1 (0 : BitVec 59) &&& x8.getD ↑x9.2.2 (0 : BitVec 59))
    (List.replicate (25 - x2.length) (Bool.true, 0, 0)) (x1 ++ x2)
  refine ⟨ds ++ List.replicate (25 - x2.length) (Bool.true, 0, 0), by simp [hds]; omega, ?_⟩
  intro x7
  rw [List.foldl_append, hf, ht, List.append_assoc, ← h1, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left x7.2]
