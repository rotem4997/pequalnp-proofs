import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2625_487
    (realize : ∀ (ops : Fin 63 → Bool) (a b : Fin 63 → Fin 89), (∀ j : Fin 63, (a j).val < 26+j.val ∧ (b j).val < 26+j.val ∧ a j ≤ b j) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 63 ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = (fun x : Fin 26 → Bool => ((List.ofFn (fun j : Fin 63 => (ops j, a j, b j))).foldl (fun w g => w ++ [
      cond g.1 (w.getD g.2.1.val false && w.getD g.2.2.val false)
        (w.getD g.2.1.val false || w.getD g.2.2.val false)]) (List.ofFn x)).getD 88 false) x)
    (search : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (ops : Fin 63 → Bool) (a b : Fin 63 → Fin 89), (∀ j : Fin 63, (a j).val < 26+j.val ∧ (b j).val < 26+j.val ∧ a j ≤ b j) ∧
      (have computed : (Fin 26 → Bool) → Bool := fun x : Fin 26 → Bool => ((List.ofFn (fun j : Fin 63 => (ops j, a j, b j))).foldl (fun w g => w ++ [
      cond g.1 (w.getD g.2.1.val false && w.getD g.2.2.val false)
        (w.getD g.2.1.val false || w.getD g.2.2.val false)]) (List.ofFn x)).getD 88 false; (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (computed fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), computed (x3 x5 x7 x9 x10) = Bool.false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size ≤ (63 : ℕ) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), (∃ x7 ∈ x1, x5 = x6 + x7) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 fun (x8 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ x5 ∈ x2, ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool), PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x4 (x3 x5 x7 x9 x10) = Bool.false := by
  intro _ _ _
  obtain ⟨ops,a,b,back,yes,no⟩ := search
  obtain ⟨C,hmono,hsize,hEval⟩ := realize ops a b back
  refine ⟨C,hmono,hsize.le,?_,?_⟩
  · intro p l h
    exact (hEval _).trans (yes p l h)
  · intro mask hm u hu v flip
    exact (hEval _).trans (no mask hm u hu v flip)
