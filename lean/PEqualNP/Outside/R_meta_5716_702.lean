import Mathlib.Combinatorics.SimpleGraph.Paths
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5716_702
    (hUniqueV :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →
        PEqualNP.TopForm.IsLeastAO x3 x5 →
        PEqualNP.TopForm.TopForm x3 x5 →
        {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 |
          ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧
          ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5,
          ∃ (x13 : Fin (2 : ℕ)),
          ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5,
            x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧
            PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
            PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
            PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
            PEqualNP.TopForm.side x5 x12 x13 = {x10} ∧
            ∀ (w : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true → w = x11}.card ≤ x1 * (x5.size + (1 : ℕ)))
    (hUniqueU :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →
        PEqualNP.TopForm.IsLeastAO x3 x5 →
        PEqualNP.TopForm.TopForm x3 x5 →
        {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 |
          ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧
          ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5,
          ∃ (x13 : Fin (2 : ℕ)),
          ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5,
            x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧
            PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
            PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
            PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
            PEqualNP.TopForm.side x5 x12 x13 = {x10} ∧
            ((PEqualNP.TopForm.tops x3 x5).filter fun t' =>
              ((PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 t' (0 : Fin (2 : ℕ)))).card = (1 : ℕ) ∧
                PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 t' (0 : Fin (2 : ℕ))) ≠ {x10} ∧
                PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 t' (1 : Fin (2 : ℕ))) x14) ∨
              ((PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 t' (1 : Fin (2 : ℕ)))).card = (1 : ℕ) ∧
                PEqualNP.TopForm.orIn x2 x5 (PEqualNP.TopForm.opnd x5 t' (1 : Fin (2 : ℕ))) ≠ {x10} ∧
                PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 t' (0 : Fin (2 : ℕ))) x14)) = ∅}.card ≤ x1 * (x5.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧ PEqualNP.TopForm.side x5 x12 x13 = {x10}}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  rcases hUniqueV with ⟨c1, hc1⟩
  rcases hUniqueU with ⟨c2, hc2⟩
  refine ⟨c1 + c2, ?_⟩
  intro n G hdec C hgirth hleast htop
  have hAO : PEqualNP.TopForm.IsAO2 n C := hleast.1
  have hAndOr : PEqualNP.EdgeOwnership.AndOrOnly C := hAO.1
  have hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C := hAO.2.1
  have hLen2 : ∀ g ∈ C.gates, g.inputs.length = 2 := hAO.2.2
  have handEval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have horEval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have hlist_split : ∀ {α : Type} (l : List α) (k : ℕ) (hk : k < l.length) (d : α),
      l = l.take k ++ l.getD k d :: l.drop (k + 1) := by
    intro α l
    induction l with
    | nil => intro k hk _; exact absurd hk (Nat.not_lt_zero k)
    | cons a t ih =>
      intro k hk d
      cases k with
      | zero => rfl
      | succ k' =>
        have hk' : k' < t.length := Nat.lt_of_succ_lt_succ hk
        change a :: t = a :: (t.take k' ++ t.getD k' d :: t.drop (k' + 1))
        exact congrArg (List.cons a) (ih k' hk' d)
  let stepW : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hfold_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl stepW init).length = init.length + gs.length := by
    intro gs init
    induction gs using List.reverseRecOn with
    | nil => simp
    | append_singleton gs g ih =>
      rw [List.foldl_append]
      change (stepW (gs.foldl stepW init) g).length = init.length + (gs ++ [g]).length
      simp only [stepW, List.length_append, List.length_singleton, ih]
      omega
  have hfold_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (i : ℕ),
      i < init.length → (gs.foldl stepW init).getD i false = init.getD i false := by
    intro gs init i hi
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [List.foldl_append]
      change (gs.foldl stepW init ++ [g.op.eval (g.inputs.map fun idx => (gs.foldl stepW init).getD idx false)]).getD i false = init.getD i false
      have hlt : i < (gs.foldl stepW init).length := by rw [hfold_len]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
      exact ih
  have hfold_take : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (k : ℕ),
      k < gs.length →
      (gs.foldl stepW init).getD (init.length + k) false =
        (gs.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op.eval
          ((gs.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs.map
            fun i => ((gs.take k).foldl stepW init).getD i false) := by
    intro gs init k hk
    have hsplit := hlist_split gs k hk ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hpre_len : (stepW ((gs.take k).foldl stepW init) (gs.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)).length =
        init.length + k + 1 := by
      change ((gs.take k).foldl stepW init ++ [_]).length = init.length + k + 1
      rw [List.length_append, List.length_singleton, hfold_len, List.length_take_of_le (Nat.le_of_lt hk)]
    rw [hfold_prefix (gs.drop (k + 1)) _ (init.length + k) (by omega)]
    change ((gs.take k).foldl stepW init ++ [_]).getD (init.length + k) false = _
    have hlen_tk : ((gs.take k).foldl stepW init).length = init.length + k := by
      rw [hfold_len, List.length_take_of_le (Nat.le_of_lt hk)]
    rw [← hlen_tk, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
    simp
  have hwire_gate : ∀ (x : Fin n → Bool) (k : ℕ), k < C.gates.length →
      PEqualNP.EdgeOwnership.gateVal n C k x =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval
          ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.map
            fun i => if i < n + k then PEqualNP.CleanedNonEdge.wireVal n C i x else false) := by
    intro x k hk
    have hinit_len : (List.ofFn x).length = n := List.length_ofFn
    have h1 : PEqualNP.EdgeOwnership.gateVal n C k x =
        (C.gates.foldl stepW (List.ofFn x)).getD ((List.ofFn x).length + k) false := by
      rw [hinit_len]; rfl
    rw [h1, hfold_take C.gates (List.ofFn x) k hk]
    congr 1
    apply List.map_congr_left
    intro i hi
    have htk_len : ((C.gates.take k).foldl stepW (List.ofFn x)).length = n + k := by
      rw [hfold_len, hinit_len, List.length_take_of_le (Nat.le_of_lt hk)]
    by_cases hilt : i < n + k
    · rw [if_pos hilt]
      have hsp : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
      change ((C.gates.take k).foldl stepW (List.ofFn x)).getD i false =
        (C.gates.foldl stepW (List.ofFn x)).getD i false
      conv_rhs => rw [hsp, List.foldl_append]
      rw [hfold_prefix (C.gates.drop k) _ i (by omega)]
    · rw [if_neg hilt]
      rw [List.getD_eq_default _ _ (by omega)]
  have hwire_input : ∀ (x : Fin n → Bool) (u : Fin n),
      PEqualNP.CleanedNonEdge.wireVal n C u.val x = x u := by
    intro x u
    change (C.gates.foldl stepW (List.ofFn x)).getD u.val false = x u
    rw [hfold_prefix C.gates (List.ofFn x) u.val (by rw [List.length_ofFn]; exact u.isLt)]
    simp [List.getD_eq_getElem?_getD, u.isLt]
  have hmono : ∀ (x y : Fin n → Bool), (∀ i : Fin n, x i = true → y i = true) →
      ∀ (w : ℕ), PEqualNP.CleanedNonEdge.wireVal n C w x = true →
        PEqualNP.CleanedNonEdge.wireVal n C w y = true := by
    intro x y hxy
    have hgen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        ∀ (w : ℕ), (gs.foldl stepW (List.ofFn x)).getD w false = true →
          (gs.foldl stepW (List.ofFn y)).getD w false = true := by
      intro gs hgs
      induction gs using List.reverseRecOn with
      | nil =>
        intro w hw
        by_cases hwlt : w < n
        · have hx : x ⟨w, hwlt⟩ = true := by
            simpa [List.getD_eq_getElem?_getD, hwlt] using hw
          simpa [List.getD_eq_getElem?_getD, hwlt] using hxy ⟨w, hwlt⟩ hx
        · exfalso
          have hdef : (List.ofFn x).getD w false = false :=
            List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
          rw [List.foldl_nil, hdef] at hw
          exact Bool.false_ne_true hw
      | append_singleton gs g ih =>
        have hgs' : ∀ g' ∈ gs, g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
          fun g' hg' => hgs g' (List.mem_append_left [g] hg')
        have ih' := ih hgs'
        intro w hw
        rw [List.foldl_append] at hw ⊢
        change (gs.foldl stepW (List.ofFn x) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn x)).getD i false)]).getD w false = true at hw
        change (gs.foldl stepW (List.ofFn y) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn y)).getD i false)]).getD w false = true
        have hlenx : (gs.foldl stepW (List.ofFn x)).length = n + gs.length := by rw [hfold_len, List.length_ofFn]
        have hleny : (gs.foldl stepW (List.ofFn y)).length = n + gs.length := by rw [hfold_len, List.length_ofFn]
        by_cases hlt : w < n + gs.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD] at hw ⊢
          exact ih' w hw
        · by_cases heq : w = n + gs.length
          · subst heq
            rw [← hlenx, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl] at hw
            rw [← hleny, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hw ⊢
            rcases hgs g (List.mem_append_right gs (List.mem_singleton_self g)) with hand | hor
            · rw [hand, handEval] at hw ⊢
              rw [List.all_eq_true] at hw ⊢
              intro b hb
              rw [List.mem_map] at hb
              rcases hb with ⟨idx, hidx, rfl⟩
              exact ih' idx (hw _ (List.mem_map.mpr ⟨idx, hidx, rfl⟩))
            · rw [hor, horEval] at hw ⊢
              rw [List.any_eq_true] at hw ⊢
              rcases hw with ⟨b, hb, hbt⟩
              rw [List.mem_map] at hb
              rcases hb with ⟨idx, hidx, rfl⟩
              exact ⟨_, List.mem_map.mpr ⟨idx, hidx, rfl⟩, ih' idx hbt⟩
          · exfalso
            have hdef : (gs.foldl stepW (List.ofFn x) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn x)).getD i false)]).getD w false = false :=
              List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton, hlenx]; omega)
            rw [hdef] at hw
            exact Bool.false_ne_true hw
    exact hgen C.gates hAndOr
  have horStep_len : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [List.foldl_append]
      change (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) [] ++ [_]).length = (gs ++ [g]).length
      rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih]
  have horStep_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List (List ℕ)) (k : ℕ),
      k < init.length → (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) init).getD k [] = init.getD k [] := by
    intro gs init k hk
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [List.foldl_append]
      have hlen : init.length ≤ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) init).length := by
        clear ih
        induction gs using List.reverseRecOn with
        | nil => exact le_rfl
        | append_singleton gs' g' ih' =>
          rw [List.foldl_append]
          change init.length ≤ (gs'.foldl (PEqualNP.CleanedNonEdge.orStep n) init ++ [_]).length
          rw [List.length_append, List.length_singleton]; omega
      change (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) init ++ [_]).getD k [] = init.getD k []
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have horSets_mem : ∀ (k g : ℕ), k < C.gates.length →
      g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] →
      g = k ∨ ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs,
          n ≤ w ∧ w < n + k ∧ g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
    let := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    intro k g hk hmem
    have hsplit := hlist_split C.gates k hk ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
    have htk_len : ((C.gates.take k).foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = k := by
      rw [horStep_len, List.length_take_of_le (Nat.le_of_lt hk)]
    have h1 : (PEqualNP.CleanedNonEdge.orSets n C).getD k [] =
        k :: (if (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or then
          ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => ((C.gates.take k).foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])
          else []) := by
      change (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
      have hlen1 : (PEqualNP.CleanedNonEdge.orStep n ((C.gates.take k).foldl (PEqualNP.CleanedNonEdge.orStep n) [])
          (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩)).length = k + 1 := by
        change ((C.gates.take k).foldl (PEqualNP.CleanedNonEdge.orStep n) [] ++ [_]).length = k + 1
        rw [List.length_append, List.length_singleton, htk_len]
      rw [horStep_prefix (C.gates.drop (k + 1)) _ k (by rw [hlen1]; exact Nat.lt_succ_self k)]
      have hget_last : ∀ (l : List (List ℕ)) (a : List ℕ) (idx : ℕ), l.length = idx → (l ++ [a]).getD idx [] = a := by
        intro l a idx hidx
        subst hidx
        simp [List.getD_eq_getElem?_getD]
      change (((C.gates.take k).foldl (PEqualNP.CleanedNonEdge.orStep n) []) ++ [_]).getD k [] = _
      rw [hget_last _ _ k htk_len]
      rw [htk_len]
      rfl
    rw [h1, List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact Or.inl rfl
    · right
      split_ifs at htail with hop
      · rw [List.mem_flatMap] at htail
        rcases htail with ⟨w, hw, hgmem⟩
        rw [List.mem_filter] at hw
        have hlt : n ≤ w ∧ w < n + k := of_decide_eq_true hw.2
        have hsp : C.gates = C.gates.take k ++ C.gates.drop k := (List.take_append_drop k C.gates).symm
        have heq_sets : ((C.gates.take k).foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [] =
            (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) [] := by
          change _ = (C.gates.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []
          conv_rhs => rw [hsp, List.foldl_append]
          rw [horStep_prefix (C.gates.drop k) _ (w - n) (by omega)]
        rw [heq_sets] at hgmem
        exact ⟨hop, w, hw.1, hlt.1, hlt.2, hgmem⟩
      · exact absurd htail List.not_mem_nil
  have hOrTrue : ∀ (x : Fin n → Bool) (k g : ℕ),
      PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g →
      PEqualNP.EdgeOwnership.gateVal n C g x = true →
      PEqualNP.EdgeOwnership.gateVal n C k x = true := by
    intro x k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro g hreach hg
      have hmem : g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] := by
        have h := hreach.2
        rwa [Nat.add_sub_cancel_left] at h
      have hklt : k < C.gates.length := by
        by_contra hge
        have hlen : (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := horStep_len C.gates
        have hdef : (PEqualNP.CleanedNonEdge.orSets n C).getD k [] = [] :=
          List.getD_eq_default _ _ (by omega)
        rw [hdef] at hmem
        exact List.not_mem_nil hmem
      rcases horSets_mem k g hklt hmem with rfl | ⟨hop, w, hwin, hnw, hwlt, hgmem⟩
      · exact hg
      · have hsub : w - n < k := by omega
        have hreach' : PEqualNP.CleanedNonEdge.OrReaches n C (n + (w - n)) g := by
          refine ⟨Nat.le_add_right n (w - n), ?_⟩
          rwa [Nat.add_sub_cancel_left]
        have hsub_true : PEqualNP.EdgeOwnership.gateVal n C (w - n) x = true :=
          ih (w - n) hsub g hreach' hg
        rw [hwire_gate x k hklt, hop, horEval, List.any_eq_true]
        refine ⟨true, List.mem_map.mpr ⟨w, hwin, ?_⟩, rfl⟩
        rw [if_pos hwlt]
        have hwn : n + (w - n) = w := by omega
        rw [← hwn]
        exact hsub_true
  have hOrTrueW : ∀ (x : Fin n → Bool) (w g : ℕ),
      PEqualNP.CleanedNonEdge.OrReaches n C w g →
      PEqualNP.EdgeOwnership.gateVal n C g x = true →
      PEqualNP.CleanedNonEdge.wireVal n C w x = true := by
    intro x w g hreach hg
    have hwn : n + (w - n) = w := Nat.add_sub_of_le hreach.1
    rw [← hwn] at hreach ⊢
    exact hOrTrue x (w - n) g hreach hg
  have hOrInTrue : ∀ (x : Fin n → Bool) (w : ℕ) (u : Fin n),
      u ∈ PEqualNP.TopForm.orIn n C w → x u = true →
      PEqualNP.CleanedNonEdge.wireVal n C w x = true := by
    letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    intro x w u hu hxu
    have hmem : (u : ℕ) = w ∨ ∃ k < C.gates.length,
        PEqualNP.CleanedNonEdge.OrReaches n C w k ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (u : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs :=
      (Finset.mem_filter.mp hu).2
    rcases hmem with heq | ⟨k, hklt, hreach, hop, huin⟩
    · rw [← heq, hwire_input x u]
      exact hxu
    · apply hOrTrueW x w k hreach
      rw [hwire_gate x k hklt, hop, horEval, List.any_eq_true]
      refine ⟨true, List.mem_map.mpr ⟨u.val, huin, ?_⟩, rfl⟩
      rw [if_pos (by have := u.isLt; omega), hwire_input x u]
      exact hxu
  have hAdj : ∀ (t : ℕ) (b : Fin 2) (j : ℕ) (u w : Fin n),
      t ∈ PEqualNP.TopForm.tops G C →
      u ∈ PEqualNP.TopForm.side C t b →
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t (1 - b)) j →
      PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput w w) = true →
      G.Adj u w := by
    letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    intro t b j u w ht hu hreach hjw
    have htmem := Finset.mem_filter.mp ht
    have htlt : t < C.gates.length := Finset.mem_range.mp htmem.1
    have htop_and : (PEqualNP.MetaComplexity.NestedCover.gateAt C t).op = PEqualNP.CircuitLowerBounds.GateOp.and :=
      htmem.2.1
    have hbelow : PEqualNP.TopForm.BelowF G C t := htmem.2.2
    let y : Fin n → Bool := PEqualNP.EdgeOwnership.pairInput u w
    have hyu : y u = true := by
      change decide (u = u ∨ u = w) = true
      simp
    have hwy : ∀ z : Fin n, PEqualNP.EdgeOwnership.pairInput w w z = true → y z = true := by
      intro z hz
      change decide (z = w ∨ z = w) = true at hz
      change decide (z = u ∨ z = w) = true
      rw [decide_eq_true_eq] at hz ⊢
      rcases hz with rfl | rfl <;> exact Or.inr rfl
    have hside_b : PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t b) y = true :=
      hOrInTrue y (PEqualNP.TopForm.opnd C t b) u hu hyu
    have hjy : PEqualNP.EdgeOwnership.gateVal n C j y = true :=
      hmono (PEqualNP.EdgeOwnership.pairInput w w) y hwy (n + j) hjw
    have hside_ob : PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t (1 - b)) y = true :=
      hOrTrueW y (PEqualNP.TopForm.opnd C t (1 - b)) j hreach hjy
    have hgt_mem : PEqualNP.MetaComplexity.NestedCover.gateAt C t ∈ C.gates := by
      change C.gates.getD t ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
      rw [List.getD_eq_getElem _ _ htlt]
      exact List.getElem_mem htlt
    have hin_len : (PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs.length = 2 :=
      hLen2 _ hgt_mem
    have hin_eq : (PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs =
        [PEqualNP.TopForm.opnd C t 0, PEqualNP.TopForm.opnd C t 1] := by
      rcases hls : (PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩
      · rw [hls] at hin_len; simp at hin_len
      · rw [hls] at hin_len; simp at hin_len
      · change [a0, a1] = [(PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs.getD 0 0,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs.getD 1 0]
        rw [hls]; rfl
      · rw [hls] at hin_len; simp at hin_len
    have hb01 : b = 0 ∨ b = 1 := by
      by_cases hb0 : b.val = 0
      · exact Or.inl (Fin.ext hb0)
      · exact Or.inr (Fin.ext (by omega))
    have hval01 : PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t 0) y = true ∧
        PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C t 1) y = true := by
      rcases hb01 with rfl | rfl
      · exact ⟨hside_b, hside_ob⟩
      · exact ⟨hside_ob, hside_b⟩
    have hgt_true : PEqualNP.EdgeOwnership.gateVal n C t y = true := by
      rw [hwire_gate y t htlt, htop_and, handEval, List.all_eq_true]
      intro val hval
      rw [List.mem_map] at hval
      rcases hval with ⟨idx, hidx, rfl⟩
      have hidxlt : idx < n + t := hRB t htlt idx hidx
      rw [if_pos hidxlt]
      rw [hin_eq, List.mem_cons, List.mem_singleton] at hidx
      rcases hidx with rfl | rfl
      · exact hval01.1
      · exact hval01.2
    have hgf : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true := hbelow y hgt_true
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), y a = true) ||
        decide (∃ a c : Fin n, G.Adj a c ∧ y a = true ∧ y c = true)) = true at hgf
    have hempty : decide (∃ a ∈ (∅ : Finset (Fin n)), y a = true) = false := by
      rw [decide_eq_false_iff_not]
      rintro ⟨a, ha, _⟩
      exact Finset.notMem_empty a ha
    rw [hempty, Bool.false_or, decide_eq_true_eq] at hgf
    rcases hgf with ⟨a, c, hac, hya, hyc⟩
    change decide (a = u ∨ a = w) = true at hya
    change decide (c = u ∨ c = w) = true at hyc
    rw [decide_eq_true_eq] at hya hyc
    rcases hya with rfl | rfl <;> rcases hyc with rfl | rfl
    · exact absurd rfl (G.ne_of_adj hac)
    · exact hac
    · exact hac.symm
    · exact absurd rfl (G.ne_of_adj hac)
  have hNoK22 : ∀ (u1 u2 v1 v2 : Fin n), u1 ≠ u2 → v1 ≠ v2 →
      G.Adj u1 v1 → G.Adj u1 v2 → G.Adj u2 v1 → G.Adj u2 v2 → False := by
    intro u1 u2 v1 v2 hu hv h11 h12 h21 h22
    have hne_u1v1 : u1 ≠ v1 := G.ne_of_adj h11
    have hne_u1v2 : u1 ≠ v2 := G.ne_of_adj h12
    have hne_u2v1 : u2 ≠ v1 := G.ne_of_adj h21
    have hne_u2v2 : u2 ≠ v2 := G.ne_of_adj h22
    let p : G.Walk u1 u1 :=
      SimpleGraph.Walk.cons h11
        (SimpleGraph.Walk.cons h21.symm
          (SimpleGraph.Walk.cons h22
            (SimpleGraph.Walk.cons h12.symm SimpleGraph.Walk.nil)))
    have hcyc : p.IsCycle := by
      refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
      · have he12 : s(u1, v1) ≠ s(v1, u2) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hne_u1v1 h1
          · exact hu h1
        have he13 : s(u1, v1) ≠ s(u2, v2) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hu h1
          · exact hne_u1v2 h1
        have he14 : s(u1, v1) ≠ s(v2, u1) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hne_u1v2 h1
          · exact hv h2
        have he23 : s(v1, u2) ≠ s(u2, v2) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hne_u2v1.symm h1
          · exact hv h1
        have he24 : s(v1, u2) ≠ s(v2, u1) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hv h1
          · exact hne_u1v1.symm h1
        have he34 : s(u2, v2) ≠ s(v2, u1) := by
          intro h; rw [Sym2.eq_iff] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hne_u2v2 h1
          · exact hu h1.symm
        simp only [p, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
          List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          not_or, not_false_eq_true, and_true]
        exact ⟨⟨he12, he13, he14⟩, ⟨he23, he24⟩, he34⟩
      · simp [p]
      · simp only [p, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
          List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          not_or, not_false_eq_true, and_true]
        exact ⟨⟨hne_u2v1.symm, hv, hne_u1v1.symm⟩, ⟨hne_u2v2, hu.symm⟩, hne_u1v2.symm⟩
    have hlen5 : 5 ≤ p.length := hgirth u1 p hcyc
    have hlen4 : p.length = 4 := rfl
    omega
  have hsub :
      {x9 ∈ PEqualNP.TopForm.Ustar G C |
        ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
        ∃ x12 ∈ PEqualNP.TopForm.tops G C,
        ∃ (x13 : Fin (2 : ℕ)),
        ∃ x14 ∈ PEqualNP.TopForm.junk G C,
          x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
          PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
          PEqualNP.TopForm.side C x12 x13 = {x10}} ⊆
      {x9 ∈ PEqualNP.TopForm.Ustar G C |
        ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
        ∃ x12 ∈ PEqualNP.TopForm.tops G C,
        ∃ (x13 : Fin (2 : ℕ)),
        ∃ x14 ∈ PEqualNP.TopForm.junk G C,
          x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
          PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
          PEqualNP.TopForm.side C x12 x13 = {x10} ∧
          ∀ (w : Fin n), PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true → w = x11} ∪
      {x9 ∈ PEqualNP.TopForm.Ustar G C |
        ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
        ∃ x12 ∈ PEqualNP.TopForm.tops G C,
        ∃ (x13 : Fin (2 : ℕ)),
        ∃ x14 ∈ PEqualNP.TopForm.junk G C,
          x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
          PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
          PEqualNP.TopForm.side C x12 x13 = {x10} ∧
          ((PEqualNP.TopForm.tops G C).filter fun t' =>
            ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (0 : Fin (2 : ℕ)))).card = (1 : ℕ) ∧
              PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (0 : Fin (2 : ℕ))) ≠ {x10} ∧
              PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t' (1 : Fin (2 : ℕ))) x14) ∨
            ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (1 : Fin (2 : ℕ)))).card = (1 : ℕ) ∧
              PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (1 : Fin (2 : ℕ))) ≠ {x10} ∧
              PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t' (0 : Fin (2 : ℕ))) x14)) = ∅} := by
    intro e he
    rw [Finset.mem_filter] at he
    rcases he with ⟨heU, u, v, rfl, t, ht, b, j, hj, hu_side, hreach, hjuv, hjvv, hside_eq⟩
    rw [Finset.mem_union]
    by_cases hV : ∀ (w : Fin n), PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true → w = v
    · left
      rw [Finset.mem_filter]
      exact ⟨heU, u, v, rfl, t, ht, b, j, hj, hu_side, hreach, hjuv, hjvv, hside_eq, hV⟩
    · right
      rw [Finset.mem_filter]
      refine ⟨heU, u, v, rfl, t, ht, b, j, hj, hu_side, hreach, hjuv, hjvv, hside_eq, ?_⟩
      have hVex : ∃ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true ∧ w ≠ v := by
        by_contra hno
        apply hV
        intro w hw
        by_contra hne
        exact hno ⟨w, hw, hne⟩
      rcases hVex with ⟨w, hjww, hwne⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro t' ht'f
      rw [Finset.mem_filter] at ht'f
      rcases ht'f with ⟨ht', h0 | h1⟩
      · rcases h0 with ⟨hcard, hne, hreach'⟩
        rcases Finset.card_eq_one.mp hcard with ⟨u', hside'⟩
        have hune : u' ≠ u := fun h => hne (by rw [hside', h])
        have hu'_side : u' ∈ PEqualNP.TopForm.side C t' 0 := by
          change u' ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' 0)
          rw [hside']; exact Finset.mem_singleton_self u'
        exact hNoK22 u u' v w (Ne.symm hune) (Ne.symm hwne)
          (hAdj t b j u v ht hu_side hreach hjvv)
          (hAdj t b j u w ht hu_side hreach hjww)
          (hAdj t' 0 j u' v ht' hu'_side hreach' hjvv)
          (hAdj t' 0 j u' w ht' hu'_side hreach' hjww)
      · rcases h1 with ⟨hcard, hne, hreach'⟩
        rcases Finset.card_eq_one.mp hcard with ⟨u', hside'⟩
        have hune : u' ≠ u := fun h => hne (by rw [hside', h])
        have hu'_side : u' ∈ PEqualNP.TopForm.side C t' 1 := by
          change u' ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' 1)
          rw [hside']; exact Finset.mem_singleton_self u'
        exact hNoK22 u u' v w (Ne.symm hune) (Ne.symm hwne)
          (hAdj t b j u v ht hu_side hreach hjvv)
          (hAdj t b j u w ht hu_side hreach hjww)
          (hAdj t' 1 j u' v ht' hu'_side hreach' hjvv)
          (hAdj t' 1 j u' w ht' hu'_side hreach' hjww)
  have hcard1 := Finset.card_le_card hsub
  have hcard2 := Finset.card_union_le
    {x9 ∈ PEqualNP.TopForm.Ustar G C |
      ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
      ∃ x12 ∈ PEqualNP.TopForm.tops G C,
      ∃ (x13 : Fin (2 : ℕ)),
      ∃ x14 ∈ PEqualNP.TopForm.junk G C,
        x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
        PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
        PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
        PEqualNP.TopForm.side C x12 x13 = {x10} ∧
        ∀ (w : Fin n), PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput w w) = Bool.true → w = x11}
    {x9 ∈ PEqualNP.TopForm.Ustar G C |
      ∃ (x10 : Fin n) (x11 : Fin n), x9 = s(x10, x11) ∧
      ∃ x12 ∈ PEqualNP.TopForm.tops G C,
      ∃ (x13 : Fin (2 : ℕ)),
      ∃ x14 ∈ PEqualNP.TopForm.junk G C,
        x10 ∈ PEqualNP.TopForm.side C x12 x13 ∧
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧
        PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧
        PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.true ∧
        PEqualNP.TopForm.side C x12 x13 = {x10} ∧
        ((PEqualNP.TopForm.tops G C).filter fun t' =>
          ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (0 : Fin (2 : ℕ)))).card = (1 : ℕ) ∧
            PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (0 : Fin (2 : ℕ))) ≠ {x10} ∧
            PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t' (1 : Fin (2 : ℕ))) x14) ∨
          ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (1 : Fin (2 : ℕ)))).card = (1 : ℕ) ∧
            PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C t' (1 : Fin (2 : ℕ))) ≠ {x10} ∧
            PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t' (0 : Fin (2 : ℕ))) x14)) = ∅}
  have hb1 := hc1 n G C hgirth hleast htop
  have hb2 := hc2 n G C hgirth hleast htop
  calc
    _ ≤ _ := hcard1
    _ ≤ _ := hcard2
    _ ≤ c1 * (C.size + 1) + c2 * (C.size + 1) := Nat.add_le_add hb1 hb2
    _ = (c1 + c2) * (C.size + 1) := (Nat.add_mul c1 c2 (C.size + 1)).symm
