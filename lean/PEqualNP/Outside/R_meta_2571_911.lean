import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2571_911
    (hLift : ∀ (n m : ℕ) (e : Fin n → Fin m) (C : Circuit) (u : ℕ),
      Monotone2 C → C.output < n+C.size → u < n+C.size →
      ∃ (D : Circuit) (v : ℕ), Monotone2 D ∧ D.size = C.size ∧
        D.output < m+D.size ∧ v < m+D.size ∧
        ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ e)) ∧
          (D.wires (List.ofFn x)).getD v false = (C.wires (List.ofFn (x ∘ e))).getD u false)
    (hSearch :
      ∃ (C : Circuit) (u : ℕ), IsAO2 21 C ∧ C.size ≤ 45 ∧ C.output < 21+C.size ∧ u < 21+C.size ∧
        (∀ i < C.size, (gateAt C i).inputs.Nodup ∧
          (21+i = C.output ∨ 21+i = u ∨ ∃ j < C.size, 21+i ∈ (gateAt C j).inputs)) ∧
        ∀ x : Fin 21 → Bool,
          (C.eval (List.ofFn x) = true ↔ ∃ (p : Fin 9) (l : Fin 12),
            (([1,3,4,5,6,7,9,10,11] : List ℕ).getD p.val 0 + l.val + 15) % 13 ∈
              ([0,1,3,9] : List ℕ) ∧
            x (Fin.castAdd 12 p) = true ∧ x (Fin.natAdd 9 l) = true) ∧
          (C.eval (List.ofFn x) = false →
            (C.wires (List.ofFn x)).getD u false = (x 9 || x 11 || x 17))) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let e : Fin 21 → Fin 25 := fun i =>
    ([1,3,4,5,6,7,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24] : List (Fin 25)).getD i.val 0
  let edge (a b : Fin 25) : Prop :=
    a.val < 12 ∧ 12 ≤ b.val ∧ (a.val+b.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧
      a.val ∉ ([0,2,8] : List ℕ)
  let localEdge (p : Fin 9) (l : Fin 12) : Prop :=
    (([1,3,4,5,6,7,9,10,11] : List ℕ).getD p.val 0 + l.val + 15)%13 ∈ ([0,1,3,9] : List ℕ)
  have edgeMatch (p : Fin 9) (l : Fin 12) :
      edge (e (Fin.castAdd 12 p)) (e (Fin.natAdd 9 l)) ↔ localEdge p l := by
    fin_cases p <;> fin_cases l <;> decide +kernel
  have pointCover : ∀ a : Fin 25, a.val < 12 → a.val ∉ ([0,2,8] : List ℕ) →
      ∃ p : Fin 9, e (Fin.castAdd 12 p) = a := by
    decide +kernel
  have lineIndex (l : Fin 12) : (e (Fin.natAdd 9 l)).val = 13+l.val := by
    fin_cases l <;> decide +kernel
  have notIsolated (a b : Fin 25) (hab : edge a b) : 13 ≤ b.val := by
    have impossible : ∀ a : Fin 25, ¬ edge a 12 := by decide +kernel
    by_contra! hb
    have eq : b = 12 := Fin.ext (by
      have low := hab.2.1
      change b.val = 12
      omega)
    exact impossible a (eq ▸ hab)
  obtain ⟨C,u,hmodel,hsize,houtput,hu,_,hbehave⟩ := hSearch
  have hm : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using hmodel.1 g hg, (hmodel.2.2 g hg).le⟩
  obtain ⟨D,w,hd,hds,hdo,hw,htransfer⟩ := hLift 21 25 e C u hm houtput hu
  refine ⟨D,w,hd,by omega,hdo,hw,?_⟩
  intro x
  have transfer := htransfer x
  have behavior := hbehave (x ∘ e)
  refine ⟨?_, ?_⟩
  · have main : D.eval (List.ofFn x) = true ↔ ∃ a b : Fin 25, edge a b ∧ x a = true ∧ x b = true := by
      rw [transfer.1, behavior.1]
      constructor
      · rintro ⟨p,l,hpl,hp,hl⟩
        exact ⟨_,_,(edgeMatch p l).mpr hpl,hp,hl⟩
      · rintro ⟨a,b,hab,ha,hb⟩
        obtain ⟨p,hp⟩ := pointCover a hab.1 hab.2.2.2
        have hline := notIsolated a b hab
        let l : Fin 12 := ⟨b.val - 13, by omega⟩
        have hl : e (Fin.natAdd 9 l) = b := Fin.ext (by rw [lineIndex]; change 13+(b.val-13) = b.val; omega)
        refine ⟨p,l,(edgeMatch p l).mp ?_, ?_, ?_⟩
        · rwa [hp,hl]
        · rwa [Function.comp_apply,hp]
        · rwa [Function.comp_apply,hl]
    simpa only [edge, and_assoc] using main
  · intro off
    rw [transfer.2, behavior.2 (transfer.1.symm.trans off)]
    rfl
