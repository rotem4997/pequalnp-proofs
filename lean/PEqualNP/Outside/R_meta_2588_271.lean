import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover

-- Use the dual description of a quadrangle to fill the complete truth table on
-- nondegenerate supports of at most four points and three lines.
theorem PEqualNP.Outside.R_meta_2588_271
    (geometry : ∀ P L : Finset (Fin 13), P.card ≤ 4 → L.card ≤ 3 →
      (∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2) →
      (∀ p : Fin 13, (L.filter fun l => p ∈ singerLines3 l).card ≤ 2) →
      L ⊆ missLines singerLines3 P →
      ∃ Q ∈ quadrangles singerLines3, P ⊆ Q ∧ L ⊆ missLines singerLines3 Q)
    (residual :
      let R (P L : Finset (Fin 13)) :=
        List.ofFn (fun u : Fin 13 => decide (u ∈ P)) ++ List.ofFn (fun v : Fin 13 => decide (v ∈ L))
      let S := singerLines3
      ∀ C : Circuit, IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
        2 ≤ andPairs 26 C →
        (∀ j < C.size, (gateAt C j).op = .and → ∀ i ∈ (gateAt C j).inputs,
          ∃ Q ∈ quadrangles S, (C.wires (R Q (missLines S Q))).getD (26+j) false ≠
            (C.wires (R Q (missLines S Q))).getD i false) →
        (∀ P L : Finset (Fin 13), P.card ≤ 4 → L.card ≤ 3 →
          (∀ l : Fin 13, (P ∩ S l).card ≤ 2) →
          (∀ p : Fin 13, (L.filter fun l => p ∈ S l).card ≤ 2) →
          C.eval (R P L) = decide (¬L ⊆ missLines S P)) →
        64 ≤ C.size) :
have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → (∀ x4 ∈ x2.gates, x4.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x4.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x2 → (∀ (x6 x7 : Fin (13 : ℕ)), x6 ∈ PEqualNP.HeptadCover.singerLines3 x7 → x2.eval ((List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x6)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) = Bool.true) → (∀ x7 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x2.eval (x1 x7) = Bool.false) → (∀ x8 < x2.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x11 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).inputs, ∃ x13 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, (x2.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false ≠ (x2.wires (x1 x13)).getD x11 Bool.false) → (64 : ℕ) ≤ x2.size := by
  let noThreePoints (P : Finset (Fin 13)) := ∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2
  let noThreeLines (L : Finset (Fin 13)) := ∀ p : Fin 13, (L.filter fun l => p ∈ singerLines3 l).card ≤ 2
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

  have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have getD_snoc_lt (l : List Bool) (x d : Bool) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq (l : List Bool) (x d : Bool) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  have getD_snoc_ne (l : List Bool) (x d : Bool) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l x d i hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have monotone_and : ∀ a a' b b' : Bool, a ≤ a' → b ≤ b' → (a && b) ≤ (a' && b') := by
    decide

  have monotone_or : ∀ a a' b b' : Bool, a ≤ a' → b ≤ b' → (a || b) ≤ (a' || b') := by
    decide

  have monotone_lists (l : List ℕ) (a b : ℕ → Bool) (le : ∀ i ∈ l, a i ≤ b i) :
      GateOp.and.eval (l.map a) ≤ GateOp.and.eval (l.map b) ∧
        GateOp.or.eval (l.map a) ≤ GateOp.or.eval (l.map b) := by
    induction l with
    | nil => exact ⟨le_rfl,le_rfl⟩
    | cons n l ih =>
      obtain ⟨conj,disj⟩ := ih (fun j hj => le j (List.mem_cons_of_mem n hj))
      have first := le n List.mem_cons_self
      exact ⟨monotone_and _ _ _ _ first conj,monotone_or _ _ _ _ first disj⟩


  have monotone_wires (gs : List Gate) (a b : List Bool)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (len : a.length = b.length)
      (ordered : ∀ i, a.getD i false ≤ b.getD i false) :
      ∀ i, (wiresFrom gs a).getD i false ≤ (wiresFrom gs b).getD i false := by
    induction gs generalizing a b with
    | nil => exact ordered
    | cons g tail ih =>
      let x := g.op.eval (g.inputs.map fun i => a.getD i false)
      let y := g.op.eval (g.inputs.map fun i => b.getD i false)
      have xy : x ≤ y := by
        change g.op.eval _ ≤ g.op.eval _
        rcases ops g List.mem_cons_self with eq | eq
        · rw [eq]
          exact (monotone_lists _ _ _ (fun i _ => ordered i)).1
        · rw [eq]
          exact (monotone_lists _ _ _ (fun i _ => ordered i)).2
      have next (i : ℕ) : (a ++ [x]).getD i false ≤ (b ++ [y]).getD i false := by
        by_cases hit : i = a.length
        · rw [getD_snoc_eq _ _ _ _ hit,getD_snoc_eq _ _ _ _ (hit.trans len)]
          exact xy
        · rw [getD_snoc_ne _ _ _ _ hit,getD_snoc_ne _ _ _ _ (by rwa [← len])]
          exact ordered i
      intro i
      change (wiresFrom tail (a ++ [x])).getD i false ≤ (wiresFrom tail (b ++ [y])).getD i false
      exact ih _ _ (fun g h => ops g (List.mem_cons_of_mem _ h)) (by simp [len]) next i

  let membershipRow (S : Finset (Fin 13)) : List Bool := List.ofFn fun t : Fin 13 => decide (t ∈ S)

  let row (P L : Finset (Fin 13)) : List Bool := membershipRow P ++ membershipRow L

  have membership_row_le {A B : Finset (Fin 13)} (sub : A ⊆ B) (i : ℕ) :
      (membershipRow A).getD i false ≤ (membershipRow B).getD i false := by
    by_cases inBounds : i < 13
    · have entry (S : Finset (Fin 13)) :
          (membershipRow S).getD i false = decide ((⟨i,inBounds⟩ : Fin 13) ∈ S) := by
        unfold membershipRow
        rw [List.getD_eq_getElem _ _ (by simpa using inBounds),List.getElem_ofFn]
      rw [entry A,entry B]
      by_cases includes : (⟨i,inBounds⟩ : Fin 13) ∈ A
      · simp [includes,sub includes]
      · simp [includes]
    · have hA : (membershipRow A).length ≤ i := by simpa [membershipRow] using Nat.le_of_not_lt inBounds
      have hB : (membershipRow B).length ≤ i := by simpa [membershipRow] using Nat.le_of_not_lt inBounds
      rw [List.getD_eq_default _ _ hA,List.getD_eq_default _ _ hB]

  have rows_le {P Q L M : Finset (Fin 13)} (points : P ⊆ Q) (lines : L ⊆ M) (i : ℕ) :
      (row P L).getD i false ≤ (row Q M).getD i false := by
    unfold row
    by_cases onLeft : i < 13
    · have hP : i < (membershipRow P).length := by simpa [membershipRow]
      have hQ : i < (membershipRow Q).length := by simpa [membershipRow]
      rw [List.getD_append _ _ _ _ hP,List.getD_append _ _ _ _ hQ]
      exact membership_row_le points i
    · have hP : (membershipRow P).length ≤ i := by simpa [membershipRow] using Nat.le_of_not_lt onLeft
      have hQ : (membershipRow Q).length ≤ i := by simpa [membershipRow] using Nat.le_of_not_lt onLeft
      rw [List.getD_append_right _ _ _ _ hP,List.getD_append_right _ _ _ _ hQ]
      simpa [membershipRow] using membership_row_le lines (i-13)

  have eval_rows_le (C : Circuit) (model : IsAO2 26 C)
      {P Q L M : Finset (Fin 13)} (points : P ⊆ Q) (lines : L ⊆ M) :
      C.eval (row P L) ≤ C.eval (row Q M) :=
    monotone_wires C.gates (row P L) (row Q M) model.1
      (by simp [row,membershipRow]) (rows_le points lines) C.output

  have complete
      (C : Circuit) (model : IsAO2 26 C)
      (positive : ∀ p l : Fin 13, p ∈ singerLines3 l → C.eval (row {p} {l}) = true)
      (negative : ∀ Q ∈ quadrangles singerLines3, C.eval (row Q (missLines singerLines3 Q)) = false)
      (P L : Finset (Fin 13)) (shortP : P.card ≤ 4) (shortL : L.card ≤ 3)
      (pShape : noThreePoints P) (lShape : noThreeLines L) :
      C.eval (row P L) = decide (¬L ⊆ missLines singerLines3 P) := by
    classical
    by_cases miss : L ⊆ missLines singerLines3 P
    · obtain ⟨Q,Qquad,pSubset,lSubset⟩ := geometry
        P L shortP shortL pShape lShape miss
      have le := eval_rows_le C model pSubset lSubset
      rw [negative Q Qquad] at le
      have answer : C.eval (row P L) = false := (by decide : ∀ b : Bool, b ≤ false → b = false) _ le
      simpa [miss] using answer
    · have clash : ∃ l ∈ L, l ∉ missLines singerLines3 P := by
        by_contra none
        apply miss
        intro l inL
        by_contra on
        exact none ⟨l,inL,on⟩
      obtain ⟨l,lMem,outside⟩ := clash
      have meet : ∃ p ∈ P, p ∈ singerLines3 l := by
        by_contra absent
        apply outside
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        apply Finset.disjoint_left.mpr
        intro p line point
        exact absent ⟨p,point,line⟩
      obtain ⟨p,pMem,incident⟩ := meet
      have low : C.eval (row {p} {l}) ≤ C.eval (row P L) :=
        eval_rows_le C model (Finset.singleton_subset_iff.mpr pMem) (Finset.singleton_subset_iff.mpr lMem)
      rw [positive p l incident] at low
      have answer : C.eval (row P L) = true := (by decide : ∀ b : Bool, true ≤ b → b = true) _ low
      simpa [miss] using answer

  intro rowOriginal C model distinct nested positive negative strict
  apply residual C model distinct nested strict
  apply complete C model ?_ negative
  intro p l h
  simpa [row,membershipRow,Finset.mem_singleton] using positive p l h
