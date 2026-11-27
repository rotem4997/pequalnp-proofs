import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7967

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
open PEqualNP.MetaComplexity.NestedCover (gateAt ReadsBack)
open PEqualNP.EdgeOwnership (InCone cones coneStep)
open PEqualNP.GenericRejection (incidenceInput)

def appendStep {α : Type} (next : List α → Gate → α) (xs : List α) (g : Gate) :
    List α := xs ++ [next xs g]

lemma fold_length {α : Type} (next : List α → Gate → α) (gs : List Gate) (xs : List α) :
    (gs.foldl (appendStep next) xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, appendStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma fold_getD_lt {α : Type} (next : List α → Gate → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    (gs.foldl (appendStep next) xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [appendStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma fold_prefix {α : Type} (next : List α → Gate → α) (gs : List Gate)
    (xs : List α) (j i : ℕ) (d : α)
    (hi : i < ((gs.take j).foldl (appendStep next) xs).length) :
    (gs.foldl (appendStep next) xs).getD i d =
      ((gs.take j).foldl (appendStep next) xs).getD i d := by
  calc
    _ = ((gs.take j ++ gs.drop j).foldl (appendStep next) xs).getD i d := by
      rw [List.take_append_drop]
    _ = _ := by rw [List.foldl_append, fold_getD_lt next _ _ i d hi]

lemma fold_at {α : Type} (next : List α → Gate → α) (gs : List Gate)
    (xs : List α) (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (appendStep next) xs).getD (xs.length + j) d =
      next ((gs.take j).foldl (appendStep next) xs) gs[j] := by
  let pre := (gs.take j).foldl (appendStep next) xs
  have hlen : pre.length = xs.length + j := by
    simp [pre, fold_length, Nat.min_eq_left (Nat.le_of_lt hj)]
  calc
    _ = ((gs.take j ++ gs.drop j).foldl (appendStep next) xs).getD (xs.length + j) d := by
      rw [List.take_append_drop]
    _ = _ := by
      rw [List.foldl_append, List.drop_eq_getElem_cons hj, List.foldl_cons]
      change ((gs.drop (j + 1)).foldl (appendStep next)
        (appendStep next pre gs[j])).getD (xs.length + j) d = _
      rw [← hlen, fold_getD_lt next _ _ _ _ (by simp [appendStep])]
      simp only [appendStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl pre.length),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rfl

def wireNext (xs : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => xs.getD i false)

def coneNext (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
    (fun w => (w - 26) :: cs.getD (w - 26) [])

def value (C : Circuit) (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ) : Bool :=
  (C.wires (incidenceInput S.toLeft S.toRight)).getD w false

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma gate_spec (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      (gateAt C j).inputs.length ≤ 2 := by
  rw [gateAt_eq C j hj]
  simpa using hm C.gates[j] (List.getElem_mem hj)

lemma input_length (S : Finset (Fin 13 ⊕ Fin 13)) :
    (incidenceInput S.toLeft S.toRight).length = 26 := by
  simp [incidenceInput]

def inputVertex (w : ℕ) (hw : w < 26) : Fin 13 ⊕ Fin 13 :=
  if hl : w < 13 then Sum.inl ⟨w, hl⟩ else Sum.inr ⟨w - 13, by omega⟩

lemma value_input (C : Circuit) (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ) (hw : w < 26) :
    value C S w = true ↔ inputVertex w hw ∈ S := by
  let x := incidenceInput S.toLeft S.toRight
  change (C.gates.foldl (appendStep wireNext) x).getD w false = true ↔ _
  rw [fold_getD_lt wireNext _ x w false (by simpa [x, input_length] using hw)]
  simp only [x, incidenceInput, List.getD_eq_getElem?_getD]
  by_cases hl : w < 13
  · rw [List.getElem?_append_left (by simpa using hl)]
    simp only [List.getElem?_ofFn, hl, ↓reduceDIte, Option.getD_some,
      decide_eq_true_eq, inputVertex, Finset.mem_toLeft]
  · have hr : w - 13 < 13 := by omega
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hl)]
    simp only [List.length_ofFn, List.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some,
      decide_eq_true_eq, inputVertex, hl, Finset.mem_toRight]

lemma value_oob (C : Circuit) (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ)
    (hw : 26 + C.gates.length ≤ w) : value C S w = false := by
  change (C.gates.foldl (appendStep wireNext) (incidenceInput S.toLeft S.toRight)).getD w false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simpa only [fold_length, input_length] using hw

lemma value_gate (C : Circuit) (hb : ReadsBack 26 C) (S : Finset (Fin 13 ⊕ Fin 13))
    (j : ℕ) (hj : j < C.gates.length) :
    value C S (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C S)) := by
  let x := incidenceInput S.toLeft S.toRight
  have hx : x.length = 26 := input_length S
  change (C.gates.foldl (appendStep wireNext) x).getD (26 + j) false = _
  rw [← hx, fold_at wireNext _ x j hj false, gateAt_eq C j hj]
  unfold wireNext
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hb j hj i (by simpa only [gateAt_eq C j hj] using hi)
  exact (fold_prefix wireNext C.gates x j i false
    (by simpa [fold_length, hx, Nat.min_eq_left (Nat.le_of_lt hj)] using hlt)).symm

lemma cone_of_read (C : Circuit) (j w i : ℕ) (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) (hn : 26 ≤ w) (hlt : w < 26 + j)
    (hi : i = w - 26 ∨ InCone 26 C i (w - 26)) : InCone 26 C i j := by
  change i ∈ (C.gates.foldl (appendStep coneNext) []).getD j []
  have h := fold_at coneNext C.gates [] j hj []
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  refine List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [gateAt_eq C j hj] using hw
  · simpa [fold_length, Nat.min_eq_left (Nat.le_of_lt hj)] using And.intro hn hlt
  · apply List.mem_cons.mpr
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      change i ∈ (C.gates.foldl (appendStep coneNext) []).getD (w - 26) [] at hi
      rw [fold_prefix coneNext C.gates [] j (w - 26) [] (by
        simp only [fold_length, List.length_nil, Nat.zero_add, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj)]
        omega)] at hi
      exact hi

lemma and_value (C : Circuit) (hb : ReadsBack 26 C) (S : Finset (Fin 13 ⊕ Fin 13))
    (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = .and) :
    value C S (26 + j) = true ↔ ∀ w ∈ (gateAt C j).inputs, value C S w = true := by
  rw [value_gate C hb S j hj, ho]
  simp [GateOp.eval, List.all_eq_true]

lemma or_value (C : Circuit) (hb : ReadsBack 26 C) (S : Finset (Fin 13 ⊕ Fin 13))
    (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = .or) :
    value C S (26 + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, value C S w = true := by
  rw [value_gate C hb S j hj, ho]
  simp [GateOp.eval, List.any_eq_true]

lemma value_mono (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    {S T : Finset (Fin 13 ⊕ Fin 13)} (hST : S ⊆ T) (w : ℕ) :
    value C S w = true → value C T w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < 26
    · rw [value_input C S w hin, value_input C T w hin]
      exact fun h => hST h
    by_cases hout : 26 + C.gates.length ≤ w
    · simp [value_oob C S w hout]
    let j := w - 26
    have hj : j < C.gates.length := by omega
    have hw : w = 26 + j := by omega
    rcases (gate_spec C hm j hj).1 with ha | ho
    · rw [hw, and_value C hb S j hj ha, and_value C hb T j hj ha]
      exact fun h i hi => ih i (by rw [hw]; exact hb j hj i hi) (h i hi)
    · rw [hw, or_value C hb S j hj ho, or_value C hb T j hj ho]
      rintro ⟨i, hi, ht⟩
      exact ⟨i, hi, ih i (by rw [hw]; exact hb j hj i hi) ht⟩

def AndFree (C : Circuit) (w : ℕ) : Prop :=
  26 ≤ w → (gateAt C (w - 26)).op ≠ .and ∧
    ∀ i, InCone 26 C i (w - 26) → (gateAt C i).op ≠ .and

lemma read_andFree (C : Circuit) (hb : ReadsBack 26 C) (j w : ℕ)
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hfree : ∀ i, InCone 26 C i j → (gateAt C i).op ≠ .and) : AndFree C w := by
  intro hn
  have hlt := hb j hj w hw
  exact ⟨hfree _ (cone_of_read C j w _ hj hw hn hlt (Or.inl rfl)),
    fun i hi => hfree i (cone_of_read C j w i hj hw hn hlt (Or.inr hi))⟩

lemma collect_witnesses (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (S : Finset (Fin 13 ⊕ Fin 13)) (ws : List ℕ)
    (h : ∀ w ∈ ws, ∃ T ⊆ S, T.card ≤ 1 ∧ value C T w = true) :
    ∃ T ⊆ S, T.card ≤ ws.length ∧ ∀ w ∈ ws, value C T w = true := by
  induction ws with
  | nil => exact ⟨∅, Finset.empty_subset _, by simp⟩
  | cons w ws ih =>
    obtain ⟨U, hUS, hU, hu⟩ := h w (List.mem_cons_self ..)
    obtain ⟨V, hVS, hV, hv⟩ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    refine ⟨U ∪ V, Finset.union_subset hUS hVS, ?_, ?_⟩
    · have hcard := Finset.card_union_le U V
      simp only [List.length_cons]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact value_mono C hm hb Finset.subset_union_left _ hu
      · exact value_mono C hm hb Finset.subset_union_right _ (hv i hi)

lemma small_witness (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (hnest : ¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j)
    (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ) :
    ∀ k : ℕ, 1 ≤ k → (k < 2 → AndFree C w) → value C S w = true →
      ∃ T ⊆ S, T.card ≤ k ∧ value C T w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk hfree htrue
    by_cases hin : w < 26
    · refine ⟨{inputVertex w hin}, Finset.singleton_subset_iff.mpr
        ((value_input C S w hin).mp htrue), by simpa using hk, ?_⟩
      exact (value_input C _ w hin).mpr (Finset.mem_singleton_self _)
    by_cases hout : 26 + C.gates.length ≤ w
    · simp [value_oob C S w hout] at htrue
    let j := w - 26
    have hj : j < C.gates.length := by omega
    have hw : w = 26 + j := by omega
    have hlt (i : ℕ) (hi : i ∈ (gateAt C j).inputs) : i < w := by
      rw [hw]
      exact hb j hj i hi
    rcases gate_spec C hm j hj with ⟨ha | ho, hlen⟩
    · have hk2 : 2 ≤ k := by
        by_contra! hk2
        exact ((hfree hk2) (by omega)).1 ha
      have hbelow (i : ℕ) (hi : InCone 26 C i j) : (gateAt C i).op ≠ .and :=
        fun hai => hnest ⟨i, j, hai, ha, hi⟩
      rw [hw, and_value C hb S j hj ha] at htrue
      obtain ⟨T, hTS, hT, ht⟩ := collect_witnesses C hm hb S (gateAt C j).inputs
        (fun i hi => ih i (hlt i hi) 1 (by decide)
          (fun _ => read_andFree C hb j i hj hi hbelow) (htrue i hi))
      exact ⟨T, hTS, hT.trans (hlen.trans hk2), by
        rw [hw, and_value C hb T j hj ha]
        exact ht⟩
    · rw [hw, or_value C hb S j hj ho] at htrue
      obtain ⟨i, hi, ht⟩ := htrue
      obtain ⟨T, hTS, hT, ht⟩ := ih i (hlt i hi) k hk
        (fun hk2 => read_andFree C hb j i hj hi ((hfree hk2) (by omega)).2) ht
      exact ⟨T, hTS, hT, by
        rw [hw, or_value C hb T j hj ho]
        exact ⟨i, hi, ht⟩⟩

end PEqualNP.Outside.L_meta_7967

theorem PEqualNP.Outside.L_meta_7967 :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x1.wires (PEqualNP.GenericRejection.incidenceInput x3.toLeft x3.toRight)).getD x2 Bool.false; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x3 : ℕ) (x4 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x2 x3 x4; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → x2 x3 → ∀ (x7 : ℕ) (x8 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x1 x3 x7 x8 = Bool.true ↔ ∃ x9 ⊆ x8, x9.card ≤ (2 : ℕ) ∧ x1 x3 x7 x9 = Bool.true := by
  intro _ _ C hm hb hnest w S
  constructor
  · exact PEqualNP.Outside.L_meta_7967.small_witness C hm hb hnest S w 2 (by decide)
      (fun h => (by omega : False).elim)
  · rintro ⟨T, hTS, _, ht⟩
    exact PEqualNP.Outside.L_meta_7967.value_mono C hm hb hTS w ht

