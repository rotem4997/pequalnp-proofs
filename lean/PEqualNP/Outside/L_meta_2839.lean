import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2839_aux

def S (w : ℕ) : Finset (Fin 9) :=
  if h : w < 9 then {⟨w, h⟩} else if w = 9 then {0, 4} else ∅

theorem getD_eq (x4 : Fin 9 → Bool) (w : ℕ) :
    (List.ofFn x4 ++ [x4 0 || x4 4]).getD w false = decide (∃ i ∈ S w, x4 i = true) := by
  unfold S
  by_cases h : w < 9
  · simp only [h, dite_true, Finset.mem_singleton, exists_eq_left]
    interval_cases w <;> rfl
  · by_cases h9 : w = 9
    · subst h9
      simp [List.getD_eq_getElem?_getD]
    · have : 10 ≤ w := by omega
      simp [h, h9, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none]
      · simp
      · simp; omega

theorem card_le (w : ℕ) (hw : w ≠ 9) : (S w).card ≤ 1 := by
  unfold S
  split_ifs <;> simp_all

end PEqualNP.Outside.L_meta_2839_aux

open PEqualNP.Outside.L_meta_2839_aux in
theorem PEqualNP.Outside.L_meta_2839 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∃ (x3 : Finset (Fin (9 : ℕ))), (x3.card ≤ (2 : ℕ) ∨ ∃ (x4 : Fin (9 : ℕ)), x3 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), x4}) ∧ ∀ (x4 : Fin (9 : ℕ) → Bool), PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x5 : ℕ) => (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ))]).getD x5 Bool.false) x1) = Decidable.decide (∃ x5 ∈ x3, x4 x5 = Bool.true) := by
  intro x1 hlen
  refine ⟨x1.toFinset.biUnion S, ?_, ?_⟩
  · match x1, hlen with
    | [], _ => simp
    | [a], _ =>
      left
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.singleton_biUnion]
      unfold S
      split_ifs <;> simp
    | [a, b], _ =>
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.biUnion_insert,
        Finset.singleton_biUnion]
      by_cases ha : a = 9
      · by_cases hb : b = 9
        · subst ha hb; left; simp [S]
        · by_cases hb' : b < 9
          · right; refine ⟨⟨b, hb'⟩, ?_⟩
            subst ha; simp [S, hb']
          · left; subst ha; simp [S, hb, hb']
      · by_cases hb : b = 9
        · by_cases ha' : a < 9
          · right; refine ⟨⟨a, ha'⟩, ?_⟩
            subst hb; simp [S, ha']
            ext x; simp; tauto
          · left; subst hb; simp [S, ha, ha']
        · left
          have h1 := card_le a ha
          have h2 := card_le b hb
          have := Finset.card_union_le (S a) (S b)
          omega
  · intro x4
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_map]
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, Function.comp_apply, id_eq, getD_eq, decide_eq_true_eq,
      Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · rintro ⟨w, hw, i, hi, hx⟩; exact ⟨i, ⟨w, hw, hi⟩, hx⟩
    · rintro ⟨i, ⟨w, hw, hi⟩, hx⟩; exact ⟨w, hw, i, hi, hx⟩
