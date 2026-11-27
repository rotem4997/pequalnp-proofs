import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
theorem PEqualNP.Outside.R_meta_5236_593
    (normalize : ∀ (n : ℕ) (C : Circuit), FanInTwo C → ReadsBack n C →
    n ≤ C.output → C.output < n + C.size →
    ∃ D : Circuit, FanInTwo D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧ D.output = C.output ∧
      D.output + 1 = n + D.size ∧ notCount D ≤ notCount C ∧
      (∀ j < D.gates.length, (gateAt D j).op = .not → ∃ s : ℕ,
      (gateAt D j).inputs.head? = some s ∧
      (∀ i < j, s = n + i → (gateAt D i).op ≠ .not) ∧
      ∀ i < j, (gateAt D i).op = .not → (gateAt D i).inputs.head? ≠ some s) ∧
      ∀ xs : List Bool, xs.length = n → D.eval xs = C.eval xs)
    (few : ∀ C : Circuit, FanInTwo C → ReadsBack 11 C → C.size ≤ 18 →
    11 ≤ C.output → C.output < 11 + C.size →
    notCount C ≤ 2 → ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2))
    (hard : ∀ C : Circuit, FanInTwo C → ReadsBack 11 C → C.size ≤ 18 →
    11 ≤ C.output → C.output < 11 + C.size →
    3 ≤ notCount C → notCount C ≤ 4 → C.output + 1 = 11 + C.size →
    (∀ j < C.gates.length, (gateAt C j).op = .not → ∃ s : ℕ,
      (gateAt C j).inputs.head? = some s ∧
      (∀ i < j, s = 11 + i → (gateAt C i).op ≠ .not) ∧
      ∀ i < j, (gateAt C i).op = .not → (gateAt C i).inputs.head? ≠ some s) → ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)).any (fun e => x e.1 && x e.2)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → (3 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (4 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x9 ++ [x9 (0 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ))]) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  intro C fan reads size out outBound _ count
  obtain ⟨D,df,dr,ds,do',last,dn,reduced,agree⟩ := normalize 11 C fan reads out outBound
  have fit : D.size ≤ 18 := ds.trans size
  have named : 11 ≤ D.output := by rwa [do']
  have valid : D.output < 11 + D.size := by omega
  obtain ⟨x,mismatch⟩ := if lo : notCount D ≤ 2 then
    few D df dr fit named valid lo
    else hard D df dr fit named valid (by omega) (dn.trans count) last reduced
  rw [agree _ (by simp)] at mismatch
  refine ⟨x,?_⟩
  simpa only [List.any_cons,List.any_nil,Bool.or_false,Prod.fst,Prod.snd,
    Bool.or_assoc] using mismatch
