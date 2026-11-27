import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4727_17
    (compile : ∀ (E : Type) (xs : List (E → Bool)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo C →
      ∃ M F : List (E → Bool), M.length ≤ PEqualNP.NotBracket.notCount C ∧
        F.length + PEqualNP.NotBracket.notCount C ≤ C.size ∧ F.Nodup ∧
        let base := fun (P : List (E → Bool)) (h : E → Bool) =>
          h = (fun _ => false) ∨ h = (fun _ => true) ∨ h ∈ xs ∨ h ∈ P
        let can := fun (P : List (E → Bool)) (h : E → Bool) =>
          base P h ∨ ∃ a ∈ M, base P a ∧ h = (fun x => !(a x))
        (∀ h ∈ F, ∃ A B : List (E → Bool), F = A ++ h :: B ∧
            ∃ a b, can A a ∧ can A b ∧
              (h = (fun x => a x && b x) ∨ h = (fun x => a x || b x))) ∧ can F (fun x => C.eval (xs.map (fun h => h x))))
    (lower : ∀ (k : ℕ), 1 ≤ k → k ≤ 4 →
      let xs : List (ℕ → Bool) := List.ofFn (fun i : Fin 10 => fun m : ℕ => m.testBit i.val)
      ∀ M F : List (ℕ → Bool), M.length ≤ k → F.length + k ≤ 19 → F.Nodup →
        let base := fun (P : List (ℕ → Bool)) (h : ℕ → Bool) =>
          h = (fun _ => false) ∨ h = (fun _ => true) ∨ h ∈ xs ∨ h ∈ P
        let can := fun (P : List (ℕ → Bool)) (h : ℕ → Bool) =>
          base P h ∨ ∃ a ∈ M, base P a ∧ h = (fun x => !(a x))
        (∀ h ∈ F, ∃ A B : List (ℕ → Bool), F = A ++ h :: B ∧
            ∃ a b, can A a ∧ can A b ∧
              (h = (fun x => a x && b x) ∨ h = (fun x => a x || b x))) → ¬ can F (fun m : ℕ => [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85].any
          (fun e : ℕ => m.testBit (e / 10) && m.testBit (e % 10)))) :
  have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (19 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x2 → PEqualNP.NotBracket.notCount x2 ≤ (4 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7 := by
  dsimp only
  intro C hf budget hn hp correctness
  let xs : List (ℕ → Bool) := List.ofFn (fun i : Fin 10 => fun m : ℕ => m.testBit i.val)
  obtain ⟨M,F,hM,hF,hnod,steps,out⟩ := compile ℕ xs C hf
  apply lower (PEqualNP.NotBracket.notCount C) hn hp M F hM (hF.trans budget) hnod steps
  have eq : (fun m => C.eval (xs.map (fun h => h m))) = (fun m : ℕ => [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85].any
          (fun e : ℕ => m.testBit (e / 10) && m.testBit (e % 10))) := by
    funext m
    let x : Fin 10 → Bool := fun i => m.testBit i.val
    have inp : xs.map (fun g => g m) = List.ofFn x := by simp [xs,x]
    rw [inp,correctness]
    simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] <;> rfl
  rwa [eq] at out
