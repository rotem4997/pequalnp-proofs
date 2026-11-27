import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_3404_1
    (plain : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 15 ≤ C.size)
    (pairs : ∀ (C : Circuit) (T : Finset (Fin 9)), FanInTwo C → T.card = 2 →
      T ≠ {0,4} → 1 ≤ notCount C → notCount C ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, decide (∃ a ∈ T, x a = true)]) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 14 ≤ C.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x2, x7 x8 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) → (14 : ℕ) ≤ x1.size := by
  intro C T legal card lo hi computes
  by_cases genuine : T.card = 2 ∧ T ≠ {0,4}
  · exact pairs C T legal genuine.1 genuine.2 lo hi computes
  let A (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let side (x : Fin 9 → Bool) := decide (∃ a ∈ T, x a = true)
  obtain ⟨pin, pinValue⟩ : ∃ pin : ℕ, ∀ (x : Fin 9 → Bool) (t : List Bool), t.length ≤ C.size →
      (A x ++ t).getD pin false = side x := by
    by_cases dup : T = {0,4}
    · subst T
      refine ⟨9, ?_⟩
      intro x t _
      rw [List.getD_append _ _ _ _ (by simp [A])]
      unfold A side
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [Bool.or_eq_true]
    · have small : T.card ≤ 1 := by
        have ne : T.card ≠ 2 := fun eq => genuine ⟨eq, dup⟩
        omega
      by_cases empty : T = ∅
      · subst T
        refine ⟨10 + C.size, ?_⟩
        intro x t ht
        rw [List.getD_eq_default _ _ (by simp [A]; omega)]
        simp [side]
      · obtain ⟨i,mem⟩ := Finset.nonempty_iff_ne_empty.mpr empty
        have single : T = {i} := by
          ext j
          simpa only [Finset.mem_singleton] using
            (show j ∈ T ↔ j = i from ⟨fun hj => Finset.card_le_one_iff.mp small hj mem,
              fun e => e ▸ mem⟩)
        subst T
        refine ⟨i.val, ?_⟩
        intro x t _
        have h : i.val < (List.ofFn x).length := by simp
        rw [List.getD_append _ _ _ _ (by simp [A]; omega)]
        unfold A side
        rw [List.getD_append _ _ _ _ h]
        simp only [Finset.mem_singleton, exists_eq_left, decide_eq_true_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some, List.getElem_ofFn]
        change x i = decide (x i = true)
        cases x i <;> rfl
  let dest (i : ℕ) := if i < 10 then i else if i = 10 then pin else i-1
  let shift (g : Gate) : Gate := ⟨g.op, g.inputs.map dest⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have align (x : Fin 9 → Bool) (t : List Bool) (ht : t.length ≤ C.size) (i : ℕ) :
      ((A x ++ [side x]) ++ t).getD i false = (A x ++ t).getD (dest i) false := by
    have len : (A x).length = 10 := by simp [A]
    by_cases low : i < 10
    · simp only [dest, low, if_true]
      have h : i < (A x).length := by omega
      have hbig : i < (A x ++ [side x]).length := by simp [len]; omega
      rw [List.getD_append (A x ++ [side x]) t false i hbig, List.getD_append (A x) [side x] false i h, List.getD_append (A x) t false i h]
    · by_cases eq : i = 10
      · subst i
        simp only [dest, lt_irrefl, if_false, if_true]
        rw [pinValue x t ht, List.getD_append _ _ _ _ (by simp [len]),
          List.getD_append_right _ _ _ _ (by omega),len]
        rfl
      · simp only [dest,low,eq,if_false]
        rw [List.getD_append_right _ _ _ _ (by simp [len]; omega),
          List.getD_append_right _ _ _ _ (by omega)]
        congr 1
  have simulate (x : Fin 9 → Bool) (gs : List Gate) (t : List Bool)
      (budget : t.length + gs.length ≤ C.size) :
      ∃ u, u.length ≤ C.size ∧ gs.foldl step ((A x ++ [side x]) ++ t) = (A x ++ [side x]) ++ u ∧
        (gs.map shift).foldl step (A x ++ t) = A x ++ u := by
    induction gs generalizing t with
    | nil => exact ⟨t,by simpa using budget,rfl,rfl⟩
    | cons g gs ih =>
      let v := g.op.eval (g.inputs.map fun i => ((A x ++ [side x]) ++ t).getD i false)
      have same : (shift g).op.eval ((shift g).inputs.map (fun i => (A x ++ t).getD i false)) = v := by
        unfold shift v
        rw [List.map_map]
        apply congrArg
        apply List.map_congr_left
        intro i _
        exact (align x t (by simp at budget; omega) i).symm
      obtain ⟨u,hu,h1,h2⟩ := ih (t ++ [v]) (by simp at budget ⊢; omega)
      refine ⟨u,hu,?_,?_⟩
      · simpa only [List.foldl_cons,step,v,List.append_assoc] using h1
      · simpa only [List.map_cons,List.foldl_cons,step,same,List.append_assoc] using h2
  let first : Gate := ⟨.or,[0,4]⟩
  let D : Circuit := ⟨first :: C.gates.map shift, dest C.output⟩
  have fan : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hm
    · simp [first]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
      simpa [shift] using legal q hq
  have bound := plain D fan (fun x => by
    have fst : step (List.ofFn x) first = A x := by
      change List.ofFn x ++ [([(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false].any id)] = List.ofFn x ++ [x 0 || x 4]
      simp [List.getD_eq_getElem?_getD, Bool.or_assoc]
    obtain ⟨u,hu,h1,h2⟩ := simulate x C.gates [] (by change 0 + C.gates.length ≤ C.gates.length; omega)
    simp only [List.append_nil] at h1 h2
    change ((C.gates.map shift).foldl step (step (List.ofFn x) first)).getD (dest C.output) false = _
    rw [fst,h2,← align x u hu C.output,← h1]
    change C.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [side x]) = _
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using computes x)
  change 15 ≤ (first :: C.gates.map shift).length at bound
  simp only [List.length_cons,List.length_map] at bound
  change 14 ≤ C.gates.length
  omega
