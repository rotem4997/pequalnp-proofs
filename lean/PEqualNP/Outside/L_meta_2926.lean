import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2926

lemma clamp (x5 : List Bool) (h : x5.length = 10) (n : ℕ) :
    x5.getD n false = x5.getD (min n 10) false := by
  by_cases hn : n ≤ 10
  · rw [min_eq_left hn]
  · have h1 : x5.length ≤ n := by omega
    have h2 : x5.length ≤ min n 10 := by omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

lemma orEval_nil : PEqualNP.CircuitLowerBounds.GateOp.or.eval [] = false := rfl

lemma orEval_one (p : Bool) : PEqualNP.CircuitLowerBounds.GateOp.or.eval [p] = p := by
  cases p <;> rfl

lemma orEval_two (p q : Bool) :
    PEqualNP.CircuitLowerBounds.GateOp.or.eval [p, q] = (p || q) := by
  cases p <;> cases q <;> rfl

end PEqualNP.Outside.L_meta_2926

theorem PEqualNP.Outside.L_meta_2926 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∃ (x3 : Fin (11 : ℕ)) (x4 : Fin (11 : ℕ)), x3 ≤ x4 ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : ℕ) => x5.getD x7 Bool.false) x1) = (x5.getD (↑x3) Bool.false || x5.getD (↑x4) Bool.false) := by
  intro x1 hlen
  match x1, hlen with
  | [], _ =>
    refine ⟨⟨10, by omega⟩, ⟨10, by omega⟩, le_refl _, ?_⟩
    intro x5 h
    have h1 : x5.length ≤ 10 := by omega
    simp only [List.map_nil, PEqualNP.Outside.L_meta_2926.orEval_nil,
      List.getD_eq_default _ _ h1, Bool.or_self]
  | [a], _ =>
    refine ⟨⟨min a 10, by omega⟩, ⟨min a 10, by omega⟩, le_refl _, ?_⟩
    intro x5 h
    simp only [List.map_cons, List.map_nil, PEqualNP.Outside.L_meta_2926.orEval_one,
      Bool.or_self]
    exact PEqualNP.Outside.L_meta_2926.clamp x5 h a
  | [a, b], _ =>
    rcases le_total (min a 10) (min b 10) with hab | hab
    · refine ⟨⟨min a 10, by omega⟩, ⟨min b 10, by omega⟩, hab, ?_⟩
      intro x5 h
      simp only [List.map_cons, List.map_nil, PEqualNP.Outside.L_meta_2926.orEval_two]
      rw [PEqualNP.Outside.L_meta_2926.clamp x5 h a, PEqualNP.Outside.L_meta_2926.clamp x5 h b]
    · refine ⟨⟨min b 10, by omega⟩, ⟨min a 10, by omega⟩, hab, ?_⟩
      intro x5 h
      simp only [List.map_cons, List.map_nil, PEqualNP.Outside.L_meta_2926.orEval_two]
      rw [PEqualNP.Outside.L_meta_2926.clamp x5 h a, PEqualNP.Outside.L_meta_2926.clamp x5 h b,
        Bool.or_comm]
  | _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega
