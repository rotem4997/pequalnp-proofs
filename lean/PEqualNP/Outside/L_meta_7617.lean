import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7617

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k)
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]

lemma foldl_append_take_getD_out {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : acc.length + k ≤ i) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d = d := by
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates x).1

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  have hget := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates x).2.1 i hi
  rw [List.getD_eq_getElem?_getD, hget, List.getD_eq_getElem?_getD]

lemma gate_val (C : Circuit) (y : List Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    (C.wires y).getD (y.length + j) false =
      g.op.eval (g.inputs.map fun k =>
        if k < y.length + j then (C.wires y).getD k false else false) := by
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    exact absurd hg (by simp)
  have hstep := (foldl_append_spec (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
    C.gates y).2.2 j g hg
  have hfull : ∀ k, k < y.length + j → (C.wires y).getD k false =
      ((C.gates.take j).foldl (fun w x => w ++
        [(fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) w x]) y).getD k false := by
    intro k hk
    unfold Circuit.wires
    exact (foldl_append_take_getD (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
      false C.gates y j k hk (le_of_lt hj)).symm
  have hout : ∀ k, ¬ k < y.length + j → false =
      ((C.gates.take j).foldl (fun w x => w ++
        [(fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) w x]) y).getD k false := by
    intro k hk
    exact (foldl_append_take_getD_out (fun w g => g.op.eval (g.inputs.map fun k => w.getD k false))
      false C.gates y j k (by omega) (le_of_lt hj)).symm
  have hmap : (g.inputs.map fun k =>
        if k < y.length + j then (C.wires y).getD k false else false) =
      g.inputs.map fun k => ((C.gates.take j).foldl (fun w x => w ++
        [(fun w g => g.op.eval (g.inputs.map fun k => w.getD k false)) w x]) y).getD k false := by
    apply List.map_congr_left
    intro k _
    split_ifs with hk
    · exact hfull k hk
    · exact hout k hk
  rw [hmap]
  unfold Circuit.wires
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some]

def S5 (n : ℕ) : Set (Set (Fin n → Bool)) :=
  {∅, Set.univ} ∪ Set.range fun (i : Fin n) => {x : Fin n → Bool | x i = Bool.true}

def W (n : ℕ) (C : Circuit) (i : ℕ) : Set (Fin n → Bool) :=
  {x | (C.wires (List.ofFn x)).getD i false = true}

lemma main (n : ℕ) (C : Circuit) (hM : Monotone2 C) :
    ∃ (x6 : Finset (Set (Fin n → Bool))), x6.card ≤ C.size ∧ (∀ x7 ∈ x6, x7 ∉ S5 n) ∧
      (∀ (x7 : Set (Set (Fin n → Bool))), S5 n ⊆ x7 →
        (∀ x9 ∈ x7, ∀ x11 ∈ x7, ∀ x13 ∈ x6, x13 = x9 ∩ x11 ∨ x13 = x9 ∪ x11 → x13 ∈ x7) →
        ∀ x10 ∈ x6, x10 ∈ x7) ∧
      ∀ (i : ℕ), W n C i ∈ S5 n ∪ ↑x6 := by
  classical
  have hempty : (∅ : Set (Fin n → Bool)) ∈ S5 n := Or.inl (by simp)
  have huniv : (Set.univ : Set (Fin n → Bool)) ∈ S5 n := Or.inl (by simp)
  have hin : ∀ i, i < n → W n C i ∈ S5 n := by
    intro i hi
    refine Or.inr ⟨⟨i, hi⟩, ?_⟩
    ext x
    simp only [W, Set.mem_setOf_eq]
    rw [wires_getD_input C _ i (by simp [hi])]
    simp [List.getD_eq_getElem?_getD, hi]
  have hbig : ∀ i, n + C.gates.length ≤ i → W n C i = ∅ := by
    intro i hi
    ext x
    simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [wires_length, List.length_ofFn]; omega)]
    simp
  obtain ⟨X, hX⟩ : ∃ X : Finset (Set (Fin n → Bool)),
      X = ((Finset.range C.gates.length).image (fun j => W n C (n + j))).filter
        (fun s => s ∉ S5 n) := ⟨_, rfl⟩
  have hXmem : ∀ i, n ≤ i → i < n + C.gates.length → W n C i ∉ S5 n → W n C i ∈ X := by
    intro i h1 h2 h3
    rw [hX, Finset.mem_filter]
    refine ⟨Finset.mem_image.2 ⟨i - n, Finset.mem_range.2 (by omega), ?_⟩, h3⟩
    congr 1
    omega
  refine ⟨X, ?_, ?_, ?_, ?_⟩
  · rw [hX]
    refine (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ?_)
    simp [Circuit.size]
  · intro s hs
    rw [hX] at hs
    exact (Finset.mem_filter.1 hs).2
  · intro x7 h5 hcl s hs
    have key : ∀ i, W n C i ∈ x7 := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        by_cases hi : i < n
        · exact h5 (hin i hi)
        by_cases hi2 : i < n + C.gates.length
        swap
        · rw [hbig i (by omega)]
          exact h5 hempty
        by_cases hs5 : W n C i ∈ S5 n
        · exact h5 hs5
        have hx6 := hXmem i (by omega) hi2 hs5
        obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨g, hget⟩ : ∃ g, C.gates[j]? = some g := ⟨_, List.getElem?_eq_getElem hj⟩
        have hmem : g ∈ C.gates := List.mem_of_getElem? hget
        obtain ⟨hop, hlen⟩ := hM g hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        have hV : ∀ k, {x : Fin n → Bool |
            (if k < n + j then (C.wires (List.ofFn x)).getD k false else false) = true} ∈ x7 := by
          intro k
          by_cases hk : k < n + j
          · have h := ih k hk
            simpa [W, hk] using h
          · have he : {x : Fin n → Bool |
                (if k < n + j then (C.wires (List.ofFn x)).getD k false else false) = true} = ∅ := by
              ext x
              simp [hk]
            rw [he]
            exact h5 hempty
        have hval : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false =
            g.op.eval (g.inputs.map fun k =>
              if k < n + j then (C.wires (List.ofFn x)).getD k false else false) := by
          intro x
          have h := gate_val C (List.ofFn x) j g hget
          rw [List.length_ofFn] at h
          exact h
        rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
        · rcases hop with hop | hop
          · have he : W n C (n + j) = Set.univ := by
              ext x
              simp only [W, Set.mem_setOf_eq, Set.mem_univ, iff_true]
              rw [hval x, hinp, hop]
              simp [GateOp.eval]
            rw [he]
            exact h5 huniv
          · have he : W n C (n + j) = ∅ := by
              ext x
              simp only [W, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
              rw [hval x, hinp, hop]
              simp [GateOp.eval]
            rw [he]
            exact h5 hempty
        · have he : W n C (n + j) = {x : Fin n → Bool |
              (if a < n + j then (C.wires (List.ofFn x)).getD a false else false) = true} := by
            ext x
            simp only [W, Set.mem_setOf_eq]
            rw [hval x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [he]
          exact hV a
        · refine hcl _ (hV a) _ (hV b) _ hx6 ?_
          rcases hop with hop | hop
          · left
            ext x
            simp only [W, Set.mem_setOf_eq, Set.mem_inter_iff]
            rw [hval x, hinp, hop]
            simp [GateOp.eval]
          · right
            ext x
            simp only [W, Set.mem_setOf_eq, Set.mem_union]
            rw [hval x, hinp, hop]
            simp [GateOp.eval]
        · rw [hinp] at hlen
          simp at hlen
    rw [hX] at hs
    obtain ⟨hs1, _⟩ := Finset.mem_filter.1 hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hs1
    exact key (n + j)
  · intro i
    by_cases hi : i < n
    · exact Or.inl (hin i hi)
    by_cases hi2 : i < n + C.gates.length
    · by_cases hs : W n C i ∈ S5 n
      · exact Or.inl hs
      · exact Or.inr (Finset.mem_coe.2 (hXmem i (by omega) hi2 hs))
    · rw [hbig i (by omega)]
      exact Or.inl hempty

end PEqualNP.Outside.L_meta_7617

theorem PEqualNP.Outside.L_meta_7617 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     let x4 : Type := Fin x1 → Bool;     have x5 : Set (Set x4) := {∅, Set.univ} ∪ Set.range fun (x5 : Fin x1) => {x6 : x4 | x6 x5 = Bool.true};     ∃ (x6 : Finset (Set x4)), x6.card ≤ x2.size ∧ (∀ x7 ∈ x6, x7 ∉ x5) ∧ (∀ (x7 : Set (Set x4)), x5 ⊆ x7 → (∀ x9 ∈ x7, ∀ x11 ∈ x7, ∀ x13 ∈ x6, x13 = x9 ∩ x11 ∨ x13 = x9 ∪ x11 → x13 ∈ x7) → ∀ x10 ∈ x6, x10 ∈ x7) ∧ ∀ (x7 : ℕ), {x8 : x4 | (x2.wires (List.ofFn x8)).getD x7 Bool.false = Bool.true} ∈ x5 ∪ ↑x6 := by
  intro x1 x2 hM
  exact PEqualNP.Outside.L_meta_7617.main x1 x2 hM
