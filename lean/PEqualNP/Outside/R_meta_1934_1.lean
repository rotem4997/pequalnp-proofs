import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1934_1
    (renameInputs : ∀ (n : ℕ) (e : Equiv.Perm (Fin n)) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (tail : List Bool),
        D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (fun i => x (e i)) ++ tail))
    (representatives : ∀ k ∈ ([0,1,3,4,6,8,9,10] : List ℕ),
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        let base := List.ofFn x ++ [x 0 && x 2]
        C.eval (base ++ [!(base.getD k false)]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
           x 6 && x 8 || x 8 && x 5)) :
    ∀ pins : List ℕ, pins.length ≤ 2 → ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, let base := List.ofFn x ++ [x 0 && x 2]
        C.eval (base ++ [GateOp.not.eval (pins.map fun i => base.getD i false)]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
           x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
           x 6 && x 8 || x 8 && x 5) := by
  intro pins _ C hfan hsize
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let j := min (pins.headD 10) 10
  have hlen (x) : (base x).length = 10 := by simp [base]
  have normalize (x) : GateOp.not.eval (pins.map fun i => (base x).getD i false) =
      !((base x).getD j false) := by
    cases pins with
    | nil =>
      change (!false) = !((base x).getD 10 false)
      rw [List.getD_eq_default _ _ (by rw [hlen])]
    | cons i rest =>
      change (!((base x).getD i false)) = !((base x).getD (min i 10) false)
      by_cases h : i ≤ 10
      · rw [min_eq_left h]
      · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by rw [hlen]; omega),
          List.getD_eq_default _ _ (by rw [hlen])]
  change ∃ x, C.eval (base x ++ [GateOp.not.eval (pins.map fun i => (base x).getD i false)]) ≠ F x
  simp_rw [normalize]
  by_cases hj : j ∈ ([0,1,3,4,6,8,9,10] : List ℕ)
  · exact representatives j hj C hfan hsize
  let v : Fin 9 → Fin 9 := ![2,1,0,5,7,3,6,4,8]
  have inv : ∀ i, v (v i) = i := by decide
  let e : Equiv.Perm (Fin 9) := ⟨v, v, inv, inv⟩
  have symmF (x) : F (fun i => x (v i)) = F x := by
    change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 ||
      x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 3 && x 4 ||
      x 6 && x 8 || x 8 && x 3) = _
    dsimp only [F]
    ac_rfl
  have jle : j ≤ 10 := Nat.min_le_right ..
  have excluded : j = 2 ∨ j = 5 ∨ j = 7 := by simp at hj; omega
  have chooseRep : ∃ k ∈ ([0,1,3,4,6,8,9,10] : List ℕ), ∀ x : Fin 9 → Bool,
      (base (fun i => x (v i))).getD j false = (base x).getD k false := by
    rcases excluded with h | h | h <;> rw [h]
    · exact ⟨0, by decide, fun _ => rfl⟩
    · exact ⟨3, by decide, fun _ => rfl⟩
    · exact ⟨4, by decide, fun _ => rfl⟩
  obtain ⟨k, hk, hread⟩ := chooseRep
  obtain ⟨D, hD, hcost, heval⟩ := renameInputs 9 e C hfan
  obtain ⟨x, hx⟩ := representatives k hk D hD (hcost ▸ hsize)
  refine ⟨fun i => x (v i), ?_⟩
  rw [symmF, hread]
  change D.eval (List.ofFn x ++ [x 0 && x 2, !((base x).getD k false)]) ≠ F x at hx
  rw [heval] at hx
  change C.eval (List.ofFn (fun i => x (v i)) ++ [x 0 && x 2, !((base x).getD k false)]) ≠ F x at hx
  change C.eval ((List.ofFn (fun i => x (v i)) ++ [x 2 && x 0]) ++
    [!((base x).getD k false)]) ≠ F x
  simpa only [List.append_assoc, List.cons_append, List.nil_append, Bool.and_comm (x 2) (x 0)] using hx
