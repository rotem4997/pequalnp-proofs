import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Install the prescribed point-pair OR as wire 26, then reuse every suffix index.
-- A monotone output is determined by its minimal true and maximal false inputs.
theorem PEqualNP.Outside.R_meta_4027_601
    (synthesize :
      let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, l ≠ 1 ∧
        (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∃ D : Circuit, D.size ≤ 58 ∧ 27 ≤ D.output ∧ D.output < 27 + D.size ∧
        PEqualNP.TopForm.IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        ∀ x, Minimal F x ∨ Maximal (fun y => ¬ F y) x →
          (D.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔ F x))
    (order : ∀ D : Circuit, PEqualNP.EdgeOwnership.AndOrOnly D →
      Monotone (fun x : Fin 26 → Bool => D.eval (List.ofFn x ++ [x 1 || x 2]))) :
∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (59 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size ∧ (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ)))) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x5 ≠ (1 : Fin (13 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true
 := by
  classical
  let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13, l ≠ 1 ∧
    (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  obtain ⟨D,hs,ho,hout,⟨hops,hback,hpair⟩,hd,rows⟩ := synthesize
  let seed : Gate := ⟨.or,[1,2]⟩
  let C : Circuit := ⟨seed :: D.gates,D.output⟩
  have init (x : Fin 26 → Bool) :
      seed.op.eval (seed.inputs.map fun i => (List.ofFn x).getD i false) = (x 1 || x 2) := by
    change (x 1 || (x 2 || false)) = _
    simp
  have suffix (x : Fin 26 → Bool) : C.wires (List.ofFn x) = D.wires (List.ofFn x ++ [x 1 || x 2]) := by
    change D.gates.foldl _ (List.ofFn x ++ [seed.op.eval (seed.inputs.map fun i => (List.ofFn x).getD i false)]) =
      D.gates.foldl _ (List.ofFn x ++ [x 1 || x 2])
    rw [init]
  have budget : C.size = D.size + 1 := rfl
  refine ⟨C,26,by omega,by change 26 ≤ D.output; omega,by change D.output < 26 + C.size; omega,
    le_rfl,by omega,?_,?_,?_⟩
  · intro j g hg
    cases j with
    | zero =>
      have e : g = seed := by simpa [C,eq_comm] using hg
      subst g
      exact ⟨Or.inr rfl,1,2,rfl,by decide,by decide,by decide⟩
    | succ j =>
      have hm : D.gates[j]? = some g := hg
      have hmem := List.mem_of_getElem? hm
      obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := by
        have hlen := hpair g hmem
        cases hh : g.inputs with
        | nil => simp [hh] at hlen
        | cons a tail =>
          cases tail with
          | nil => simp [hh] at hlen
          | cons b tail =>
            cases tail with
            | nil => exact ⟨_,_,rfl⟩
            | cons z zs => simp [hh] at hlen
      have hau := hd g hmem
      have hj : j < D.gates.length := by
        by_contra! hn
        rw [List.getElem?_eq_none hn] at hm
        contradiction
      have he : PEqualNP.MetaComplexity.NestedCover.gateAt D j = g := by
        change D.gates.getD j _ = g
        simp only [List.getD_eq_getElem?_getD,hm,Option.getD_some]
      have hb := hback j hj
      rw [he,hab] at hb
      refine ⟨hops g hmem,a,b,hab,by simpa [hab] using hau,?_,?_⟩
      · have := hb a (by simp)
        omega
      · have := hb b (by simp)
        omega
  · intro x
    rw [suffix]
    let w := List.ofFn x ++ [x 1 || x 2]
    let step := fun (u : List Bool) (g : Gate) => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]
    have keep (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
        (gs.foldl step u).getD i false = u.getD i false := by
      induction gs generalizing u with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons,ih (step u g) (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi
    change (D.gates.foldl step w).getD 26 false = _
    rw [keep _ _ _ (by simp [w])]
    exact List.getD_append_right _ _ _ _ (by simp) |>.trans (by simp)
  · intro x
    change (C.wires (List.ofFn x)).getD D.output false = true ↔ F x
    rw [suffix]
    change D.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔ F x
    have mono := order D hops
    constructor
    · intro hx
      by_contra h
      obtain ⟨y,hy,hm⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬ F z) x h
      have hxy := mono hy
      change D.eval (List.ofFn x ++ [x 1 || x 2]) ≤ D.eval (List.ofFn y ++ [y 1 || y 2]) at hxy
      rw [hx] at hxy
      exact hm.1 ((rows y (Or.inr hm)).1 (top_unique hxy))
    · intro hx
      obtain ⟨y,hy,hm⟩ := exists_minimal_le_of_wellFoundedLT F x hx
      have hxy := mono hy
      change D.eval (List.ofFn y ++ [y 1 || y 2]) ≤ D.eval (List.ofFn x ++ [x 1 || x 2]) at hxy
      rw [(rows y (Or.inl hm)).2 hm.1] at hxy
      exact top_unique hxy
