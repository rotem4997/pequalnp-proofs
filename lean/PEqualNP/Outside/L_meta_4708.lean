import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4708

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



theorem split (n : ℕ) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hrb : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j) :
    ∀ w, w < n + gs.length → ∃ (T A : Finset ℕ), (∀ i ∈ T, i < n) ∧
      (∀ j ∈ A, ∃ hj : j < gs.length, gs[j].op = GateOp.and) ∧
      ∀ x : List Bool, x.length = n → ((run gs x).getD w false = true ↔
        (∃ i ∈ T, x.getD i false = true) ∨ ∃ j ∈ A, (run gs x).getD (n + j) false = true) := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h : w < n
    · refine ⟨{w}, ∅, by simpa using h, by simp, fun x hx => ?_⟩
      rw [run_input _ _ _ (by omega)]
      simp
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      rcases hop _ (List.getElem_mem hj) with ho | ho
      · exact ⟨∅, {j}, by simp, fun k hk => by
          obtain rfl := Finset.mem_singleton.1 hk
          exact ⟨hj, ho⟩, fun x hx => by simp⟩
      · have hi : ∀ i : {i // i ∈ gs[j].inputs}, ∃ (T A : Finset ℕ), (∀ i ∈ T, i < n) ∧
            (∀ j ∈ A, ∃ hj : j < gs.length, gs[j].op = GateOp.and) ∧
            ∀ x : List Bool, x.length = n → ((run gs x).getD i.1 false = true ↔
              (∃ i ∈ T, x.getD i false = true) ∨ ∃ j ∈ A, (run gs x).getD (n + j) false = true) :=
          fun i => ih i.1 (hrb j hj i.1 i.2) (by have := hrb j hj i.1 i.2; omega)
        choose T A h1 h2 h3 using hi
        refine ⟨gs[j].inputs.attach.toFinset.biUnion T, gs[j].inputs.attach.toFinset.biUnion A,
          fun i hi => ?_, fun k hk => ?_, fun x hx => ?_⟩
        · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 hi
          exact h1 a i ha
        · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 hk
          exact h2 a k ha
        · have e := run_gate gs x j hj
          rw [hx] at e
          rw [e, ho]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
          constructor
          · rintro ⟨i, hi, hv⟩
            rw [if_pos (hrb j hj i hi)] at hv
            rcases (h3 ⟨i, hi⟩ x hx).1 hv with ⟨t, ht, hv⟩ | ⟨t, ht, hv⟩
            · exact Or.inl ⟨t, Finset.mem_biUnion.2 ⟨⟨i, hi⟩, by simp, ht⟩, hv⟩
            · exact Or.inr ⟨t, Finset.mem_biUnion.2 ⟨⟨i, hi⟩, by simp, ht⟩, hv⟩
          · rintro (⟨t, ht, hv⟩ | ⟨t, ht, hv⟩)
            · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 ht
              exact ⟨a.1, a.2, by
                rw [if_pos (hrb j hj a.1 a.2)]; exact (h3 a x hx).2 (Or.inl ⟨t, ha, hv⟩)⟩
            · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.1 ht
              exact ⟨a.1, a.2, by
                rw [if_pos (hrb j hj a.1 a.2)]; exact (h3 a x hx).2 (Or.inr ⟨t, ha, hv⟩)⟩

end PEqualNP.Outside.L_meta_4708

open PEqualNP.Outside.L_meta_4708 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4708 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x2.output < x1 + x2.size → (∀ (x6 : Fin x1), (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x6)) = Bool.false) → ∃ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x2.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ ∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true ↔ ∃ x9 ∈ x7, PEqualNP.EdgeOwnership.gateVal x1 x2 x9 x8 = Bool.true := by
  intro n C hC hrb hout hs
  have hga : ∀ (j : ℕ) (hj : j < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
    fun j hj => List.getD_eq_getElem _ _ hj
  obtain ⟨T, A, h1, h2, h3⟩ := split n C.gates (fun g hg => by simpa using (hC g hg).1)
    (fun j hj i hi => hrb j hj i (by rw [hga j hj]; exact hi)) C.output hout
  refine ⟨A, fun j hj => ?_, fun x => ?_⟩
  · obtain ⟨hjl, ho⟩ := h2 j hj
    exact ⟨hjl, by rw [hga j hjl]; exact ho⟩
  · refine (h3 (List.ofFn x) (by simp)).trans ⟨?_, Or.inr⟩
    rintro (⟨i, hi, _⟩ | h)
    · exfalso
      have hin := h1 i hi
      have hf := hs ⟨i, hin⟩
      have ht := (h3 (List.ofFn fun k : Fin n => decide (k = ⟨i, hin⟩)) (by simp)).2
        (Or.inl ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hin]⟩)
      exact Bool.false_ne_true (hf.symm.trans ht)
    · exact h
