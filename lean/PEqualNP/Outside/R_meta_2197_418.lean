import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2197_418
    (positive : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 12 →
      (∃ s∈([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), let x := (fun i : Fin 9 => s.testBit i.val); D.eval (List.ofFn x ++ [x 0 || x 1])=false) ∨
      (∃ s∈([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), let x := (fun i : Fin 9 => s.testBit i.val); D.eval (List.ofFn x ++ [x 0 || x 1])=true))
    (multiple : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size=13 → D.output=22 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D →
      (∀ u : Fin 9, ∃ g∈D.gates,u.val∈g.inputs) → 2 ≤ PEqualNP.NotBracket.notCount D → PEqualNP.NotBracket.notCount D ≤ 5 →
      ∃ x : Fin 9 → Bool, (!D.eval (List.ofFn x ++ [x 0 || x 1])) ≠ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
    (remove : ∀ (n : ℕ) (a b : Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.NotBracket.notCount C ≤ 1 →
      f (fun _ => false)=false → f (fun _ => true)=true →
      (∀ x, (!C.eval (List.ofFn x ++ [x a || x b]))=f x) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size ∧
        ∀ x, D.eval (List.ofFn x ++ [x a || x b]) = f x)
    (budget : ∀ (n : ℕ) (a b : Fin n) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool),
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j,j≠i → x j=y j) ∧
        (x a || x b)=(y a || y b) ∧ f x≠f y) →
      (∀ x,C.eval (List.ofFn x ++ [x a || x b])=f x) →
      n + PEqualNP.NotBracket.notCount C ≤ C.size+1) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ (x4 : Fin x1.length), ∀ x5 ∈ (x1.get x4).inputs, x5 < (10 : ℕ) + ↑x4) →         (∀ (x5 : Fin (9 : ℕ)), ∃ x6 ∈ x1, ↑x5 ∈ x6.inputs) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ))]);             (!x7.getD (22 : ℕ) Bool.false) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro gates length fan back reads
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,22⟩
  let f := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  have agree : ∀ x : Fin 9 → Bool, f x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by decide +kernel
  by_contra! no
  have computes : ∀ x : Fin 9 → Bool, (!C.eval (List.ofFn x ++ [x 0 || x 1]))=f x := fun x => (not_ne_iff.mp (no x)).trans (agree x).symm
  have size : C.size=13 := length
  by_cases few : PEqualNP.NotBracket.notCount C ≤ 1
  · obtain ⟨D,md,sd,eval⟩ := remove 9 0 1 C f fan few (by decide) (by decide) computes
    have p : ∀ s∈([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), f (fun i : Fin 9 => s.testBit i.val)=true := by decide +kernel
    have q : ∀ s∈([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), f (fun i : Fin 9 => s.testBit i.val)=false := by decide +kernel
    rcases positive D md (by omega) with ⟨s,mem,miss⟩|⟨s,mem,miss⟩
    · exact Bool.noConfusion (miss.symm.trans ((eval (fun i : Fin 9 => s.testBit i.val)).trans (p s mem)))
    · exact Bool.noConfusion (miss.symm.trans ((eval (fun i : Fin 9 => s.testBit i.val)).trans (q s mem)))
  · have rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 C := by
      intro i hi u hu
      apply back ⟨i,hi⟩ u
      change u ∈ (gates.getD i ⟨.or,[]⟩).inputs at hu
      rw [List.getD_eq_getElem _ _ (show i<gates.length from hi)] at hu
      exact hu
    let nb : Fin 9 → Fin 9 := ![1,0,1,2,3,0,1,2,3]
    let lo := fun (i j : Fin 9) => decide (j=nb i)
    let hi := fun (i j : Fin 9) => decide (j=nb i ∨ j=i)
    have sensitive : ∀ i, (∀ j,j≠i → lo i j=hi i j) ∧
        (lo i 0 || lo i 1)=(hi i 0 || hi i 1) ∧ (!f (lo i))≠(!f (hi i)) := by decide +kernel
    have table' (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 1])=(!f x) := by rw [←computes x,Bool.not_not]
    have cap := budget 9 0 1 C (fun x => !f x) fan (fun i => ⟨lo i,hi i,sensitive i⟩) table'
    obtain ⟨x,h⟩ := multiple C fan size rfl rb reads (by omega) (by omega)
    exact h (computes x)
