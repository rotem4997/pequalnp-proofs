import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Keep the supplied triples in the fourteen-row search. Each of the other
-- seven rows appends four line OR gates, one point AND gate and one output OR.
theorem PEqualNP.Outside.R_meta_4919_217
    (core : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 68 ∧ ∀ x : Fin 42 → Bool,
      let L (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21 + (3 * j.val + d) % 21))
      C.eval ((List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
          List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20)) = true ↔
        ∃ u v : Fin 42, (u.val < 21 ∧ u.val % 3 ≠ 2 ∧ 21 ≤ v.val ∧
          (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧ x u = true ∧ x v = true)
    (tail : ∀ C : Circuit, Monotone2 C → ∃ D, Monotone2 D ∧ D.size ≤ C.size + 42 ∧
      ∀ w : List Bool, w.length = 56 → (D.eval w = true ↔ C.eval w = true ∨
        ∃ u v : Fin 42, (u.val < 21 ∧ u.val % 3 = 2 ∧ 21 ≤ v.val ∧
          (v.val + 21 - u.val) % 21 ∈ ([0,5,7,17,20] : List ℕ)) ∧
          w.getD u.val false = true ∧ w.getD v.val false = true)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (110 : ℕ) ∧       ∀ (x2 : Fin (42 : ℕ) → Bool),         x1.eval               (have x3 : Fin (7 : ℕ) → ℕ → Bool := fun (x3 : Fin (7 : ℕ)) (x4 : ℕ) => x2 (Fin.ofNat (42 : ℕ) ((21 : ℕ) + ((3 : ℕ) * ↑x3 + x4) % (21 : ℕ)));               (List.ofFn x2 ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ)) ++ List.ofFn fun (x4 : Fin (7 : ℕ)) => x3 x4 (5 : ℕ) || x3 x4 (17 : ℕ) || x3 x4 (20 : ℕ)) =             Bool.true ↔           ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  obtain ⟨C,hC,small,coreEval⟩ := core
  obtain ⟨D,hD,budget,tailEval⟩ := tail C hC
  refine ⟨D,hD,by omega,?_⟩
  intro x
  let L (j : Fin 7) (d : ℕ) := x (Fin.ofNat 42 (21 + (3 * j.val + d) % 21))
  let w := (List.ofFn x ++ List.ofFn (fun j : Fin 7 => L j 5 || L j 17)) ++
    List.ofFn (fun j : Fin 7 => L j 5 || L j 17 || L j 20)
  have readInput (u : Fin 42) : w.getD u.val false = x u := by
    dsimp only [w]
    rw [List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact u.isLt),List.getElem_ofFn]
  have first := coreEval x
  change C.eval w = true ↔ _ at first
  change D.eval w = true ↔ _
  rw [tailEval w (by simp [w]),first]
  simp only [readInput]
  constructor
  · rintro (⟨u,v,⟨a,_,b,c⟩,d,e⟩ | ⟨u,v,⟨a,_,b,c⟩,d,e⟩)
    all_goals exact ⟨u,v,⟨a,b,c⟩,d,e⟩
  · rintro ⟨u,v,⟨a,b,c⟩,d,e⟩
    by_cases part : u.val % 3 = 2
    · exact Or.inr ⟨u,v,⟨a,part,b,c⟩,d,e⟩
    · exact Or.inl ⟨u,v,⟨a,part,b,c⟩,d,e⟩
