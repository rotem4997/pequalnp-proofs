import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.R_meta_3120_608
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) → 13 + notCount C ≤ C.size)
    (fewNot : ∀ i ∈ ([5, 6] : List (Fin 9)), ∀ C : Circuit, FanInTwo C →
      notCount C ≤ 1 → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!x i]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) :
    ∀ x1 ∈ [(5 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))] ++ [!x5 x1]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x3.size := by
  intro i hi C hfan computes
  by_cases few : notCount C ≤ 1
  · by_contra hsize
    obtain ⟨x, hx⟩ := fewNot i hi C hfan few (by omega)
    exact hx (computes x)
  · let pref : List Gate := [⟨.and, [0, 3]⟩, ⟨.not, [i.val]⟩]
    let D : Circuit := ⟨pref ++ C.gates, C.output⟩
    have hfanD : FanInTwo D := by
      intro g hg
      change g ∈ pref ++ C.gates at hg
      rcases List.mem_append.mp hg with hp | hc
      · simp only [pref, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨Or.inl rfl, by decide⟩
        · exact ⟨Or.inr (Or.inr rfl), by simp⟩
      · exact hfan g hc
    have pin (x : Fin 9 → Bool) :
        (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt),
        List.getElem_ofFn]
    have evalD (x : Fin 9 → Bool) :
        D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [x 0 && x 3] ++ [!x i]) := by
      change ((pref ++ C.gates).foldl _ (List.ofFn x)).getD C.output false =
        (C.gates.foldl _ (List.ofFn x ++ [x 0 && x 3] ++ [!x i])).getD C.output false
      rw [List.foldl_append]
      congr 2
      change
        List.ofFn x ++ [(List.ofFn x).getD 0 false &&
          ((List.ofFn x).getD 3 false && true)] ++
        [!((List.ofFn x ++ [(List.ofFn x).getD 0 false &&
          ((List.ofFn x).getD 3 false && true)]).getD i.val false)] =
          List.ofFn x ++ [x 0 && x 3] ++ [!x i]
      rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt), pin]
      have zero : (List.ofFn x).getD 0 false = x 0 := rfl
      have three : (List.ofFn x).getD 3 false = x 3 := rfl
      rw [zero, three, Bool.and_true]
    have h := binaryBound D hfanD (fun x => (evalD x).trans (computes x))
    have hsizeD : D.size = C.size + 2 := by
      change (pref ++ C.gates).length = C.gates.length + 2
      rw [List.length_append]
      change 2 + C.gates.length = C.gates.length + 2
      omega
    have hnotD : notCount D = notCount C + 1 := by
      change ((pref ++ C.gates).filter _).length = (C.gates.filter _).length + 1
      rw [List.filter_append, List.length_append]
      change 1 + (C.gates.filter _).length = (C.gates.filter _).length + 1
      omega
    omega
