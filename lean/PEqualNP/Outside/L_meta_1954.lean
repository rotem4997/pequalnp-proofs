import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_1954

open PEqualNP.CircuitLowerBounds

theorem fold_ext (f : List ℕ → Gate → ℕ) (gs : List Gate) :
    ∀ init : List ℕ, ∃ t, gs.foldl (fun d g => d ++ [f d g]) init = init ++ t := by
  induction gs with
  | nil => intro init; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro init
    obtain ⟨t, ht⟩ := ih (init ++ [f init g])
    refine ⟨[f init g] ++ t, ?_⟩
    show List.foldl _ (init ++ [f init g]) gs = _
    rw [ht]
    simp

theorem fold_len (f : List ℕ → Gate → ℕ) (gs : List Gate) :
    ∀ init : List ℕ, (gs.foldl (fun d g => d ++ [f d g]) init).length = init.length + gs.length := by
  induction gs with
  | nil => intro init; simp
  | cons g gs ih =>
    intro init
    show (List.foldl _ (init ++ [f init g]) gs).length = _
    rw [ih]
    simp
    omega

theorem fold_split (f : List ℕ → Gate → ℕ) (gs : List Gate) (init : List ℕ) (j : ℕ) :
    gs.foldl (fun d g => d ++ [f d g]) init =
      (gs.drop j).foldl (fun d g => d ++ [f d g]) ((gs.take j).foldl (fun d g => d ++ [f d g]) init) := by
  conv_lhs => rw [← List.take_append_drop j gs]
  rw [List.foldl_append]

theorem fold_at (f : List ℕ → Gate → ℕ) (gs : List Gate) (init : List ℕ) (j : ℕ)
    (hj : j < gs.length) :
    (gs.foldl (fun d g => d ++ [f d g]) init).getD (init.length + j) 0 =
      f ((gs.take j).foldl (fun d g => d ++ [f d g]) init) gs[j] := by
  rw [fold_split f gs init j, List.drop_eq_getElem_cons hj]
  have hlen : ((gs.take j).foldl (fun d g => d ++ [f d g]) init).length = init.length + j := by
    rw [fold_len]
    simp
    omega
  generalize ((gs.take j).foldl (fun d g => d ++ [f d g]) init) = L at hlen ⊢
  show (List.foldl _ (L ++ [f L gs[j]]) _).getD _ 0 = _
  obtain ⟨t, ht⟩ := fold_ext f (gs.drop (j + 1)) (L ++ [f L gs[j]])
  rw [ht, ← hlen]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem fold_prefix_getD (f : List ℕ → Gate → ℕ) (gs : List Gate) (init : List ℕ) (j i : ℕ)
    (hi : i < ((gs.take j).foldl (fun d g => d ++ [f d g]) init).length) :
    (gs.foldl (fun d g => d ++ [f d g]) init).getD i 0 =
      ((gs.take j).foldl (fun d g => d ++ [f d g]) init).getD i 0 := by
  rw [fold_split f gs init j]
  obtain ⟨t, ht⟩ := fold_ext f (gs.drop j) ((gs.take j).foldl (fun d g => d ++ [f d g]) init)
  rw [ht]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem input_le_lineDegree (g : Gate) (d : List ℕ) (c : ℕ) (hc : c ∈ g.inputs) :
    d.getD c 0 ≤ g.lineDegree d := by
  have hm : d.getD c 0 ∈ g.inputs.map (fun i => d.getD i 0) :=
    List.mem_map.mpr ⟨c, hc, rfl⟩
  unfold Gate.lineDegree
  split_ifs
  · exact List.le_sum_of_mem hm
  · exact le_foldr_max hm

theorem deg_pos (C : Circuit) (n : ℕ) (A B : Finset ℕ) (hAB : ∀ i < n, i ∈ A ∨ i ∈ B)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hne : ∀ g ∈ C.gates, g.inputs ≠ []) :
    ∀ w, w < n + C.gates.length →
      0 < (C.lineDegrees n A).getD w 0 + (C.lineDegrees n B).getD w 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hwn : w < n
  · have hA : ∀ M : Finset ℕ, (C.lineDegrees n M).getD w 0 = if w ∈ M then 1 else 0 := by
      intro M
      unfold Circuit.lineDegrees
      obtain ⟨t, ht⟩ := fold_ext (fun d g => g.lineDegree d) C.gates
        ((List.range n).map fun i => if i ∈ M then 1 else 0)
      rw [ht]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hwn]
    rw [hA, hA]
    rcases hAB w hwn with h | h <;> simp [h]
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hg := hne _ (List.getElem_mem hj)
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hg
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    have hil : i < n + j := hRB j hj i (by rw [hga]; exact hi)
    have step : ∀ M : Finset ℕ,
        (C.lineDegrees n M).getD i 0 ≤ (C.lineDegrees n M).getD (n + j) 0 := by
      intro M
      unfold Circuit.lineDegrees
      have h1 := fold_at (fun d g => g.lineDegree d) C.gates
        ((List.range n).map fun i => if i ∈ M then 1 else 0) j hj
      simp only [List.length_map, List.length_range] at h1
      rw [h1, fold_prefix_getD (fun d g => g.lineDegree d) C.gates _ j i
        (by rw [fold_len]; simp; omega)]
      exact input_le_lineDegree _ _ _ hi
    have h1 := ih i (by omega) (by omega)
    have h2 := step A
    have h3 := step B
    omega

end PEqualNP.Outside.L_meta_1954

theorem PEqualNP.Outside.L_meta_1954 : (∀ (N230 : ℕ) (C230 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g230 ∈ C230.gates, (g230.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g230.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g230.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N230 + N230) C230) → (∀ j230x2 < C230.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i230x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x2 0 = 0) ∨ (∀ h230 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD h230 0 = 0)) → PEqualNP.MetaComplexity.circuitFun (N230 + N230) C230 (Fin.append (fun u230 : Fin N230 => true) (fun u230x1 : Fin N230 => false)) = false → ∀ mixed230 : ℕ → Prop, mixed230 = (fun i230 : ℕ => 0 < (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD i230 0 ∧ 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230 0) → ∀ cone230 : ℕ → Prop, cone230 = (fun j230 : ℕ => j230 < C230.gates.length ∧ mixed230 (N230 + N230 + j230) ∧ Relation.ReflTransGen (fun a230 b230 : ℕ => a230 < b230 ∧ ∃ f230 : Fin C230.gates.length, b230 = N230 + N230 + f230.val ∧ a230 ∈ (C230.gates.get f230).inputs) (N230 + N230 + j230) C230.output) → (∀ j230x1 : ℕ, cone230 j230x1 → (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i230x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).inputs, 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x1 0) ∧ Set.ncard {j230x3 : ℕ | cone230 j230x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x3).op = PEqualNP.CircuitLowerBounds.GateOp.or} + Set.ncard {j230x4 : ℕ | cone230 j230x4} = Set.ncard {js230 : ℕ × ℕ | cone230 js230.1 ∧ js230.2 < 2 ∧ (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230.1).inputs.getD js230.2 0) 0 = 0} + Set.ncard {js230x1 : ℕ × ℕ | cone230 js230x1.1 ∧ js230x1.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x1.1).inputs.getD js230x1.2 0)} ∧ Set.ncard {j230x5 : ℕ | cone230 j230x5} ≤ Set.ncard {js230x2 : ℕ × ℕ | cone230 js230x2.1 ∧ js230x2.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x2.1).inputs.getD js230x2.2 0)} + 1) → (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → (∀ (N241 : ℕ) (I241 : Fin N241 → Fin N241 → Prop) [DecidableRel I241] (C241 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g241 ∈ C241.gates, (g241.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g241.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g241.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N241 + N241) C241) → (∀ j241 < C241.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241 0 = 0) ∨ (∀ h241 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241).inputs, (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241 0 = 0)) → (∀ p241 p241x1 w241 w241x1 : Fin N241, p241 ≠ p241x1 → w241 ≠ w241x1 → I241 p241 w241 → I241 p241x1 w241 → I241 p241 w241x1 → I241 p241x1 w241x1 → False) → (∃ p241x2 w241x2 : Fin N241, I241 p241x2 w241x2) → (∀ p241x3 w241x3 : Fin N241, I241 p241x3 w241x3 → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append (fun a241 : Fin N241 => decide (a241 = p241x3)) (fun a241x1 : Fin N241 => decide (a241x1 = w241x3))) = true) → (∀ x241 y241 : Fin N241 → Bool, (Finset.univ.filter (fun l241 : Fin N241 => y241 l241 = true)).card ≤ 1 → (¬ ∃ p241x4 w241x4 : Fin N241, I241 p241x4 w241x4 ∧ x241 p241x4 = true ∧ y241 w241x4 = true) → PEqualNP.MetaComplexity.circuitFun (N241 + N241) C241 (Fin.append x241 y241) = false) → ∀ mixed241 : ℕ → Prop, mixed241 = (fun i241x1 : ℕ => 0 < (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD i241x1 0 ∧ 0 < (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241x1 0) → ∀ cone241 : ℕ → Prop, cone241 = (fun j241x1 : ℕ => j241x1 < C241.gates.length ∧ mixed241 (N241 + N241 + j241x1) ∧ Relation.ReflTransGen (fun a241x2 b241 : ℕ => a241x2 < b241 ∧ ∃ f241 : Fin C241.gates.length, b241 = N241 + N241 + f241.val ∧ a241x2 ∈ (C241.gates.get f241).inputs) (N241 + N241 + j241x1) C241.output) → ∀ gok241 : (Fin N241 → Bool) → ℕ → Prop, gok241 = (fun (x241x1 : Fin N241 → Bool) (j241x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i241x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x2).inputs, (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD i241x2 0 = 0 ∧ (C241.wires (List.ofFn (Fin.append x241x1 (fun u241 : Fin N241 => false)))).getD i241x2 false = true) → ∀ step241 : (Fin N241 → Bool) → ℕ → ℕ → Prop, step241 = (fun (x241x2 : Fin N241 → Bool) (j241x3 j241x4 : ℕ) => cone241 j241x4 ∧ N241 + N241 + j241x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x4).inputs ∧ gok241 x241x2 j241x4) → ∀ lvx241 : (Fin N241 → Bool) → ℕ → Prop, lvx241 = (fun (x241x3 : Fin N241 → Bool) (j241x5 : ℕ) => cone241 j241x5 ∧ gok241 x241x3 j241x5 ∧ ∃ j241x6 : ℕ, N241 + N241 + j241x6 = C241.output ∧ Relation.ReflTransGen (step241 x241x3) j241x5 j241x6) → ∀ slot241 : ℕ → ℕ → Prop, slot241 = (fun h241x1 j241x7 : ℕ => cone241 j241x7 ∧ h241x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x7).inputs ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD h241x1 0 = 0) → ∀ ap241 : ℕ → Fin N241 → Prop, ap241 = (fun (h241x2 : ℕ) (p241x5 : Fin N241) => ∃ j241x8 : ℕ, slot241 h241x2 j241x8 ∧ lvx241 (fun a241x3 : Fin N241 => decide (a241x3 = p241x5)) j241x8) → ∀ lh241 : ℕ → Fin N241 → Prop, lh241 = (fun (h241x3 : ℕ) (w241x5 : Fin N241) => (C241.wires (List.ofFn (Fin.append (fun u241x1 : Fin N241 => false) (fun a241x4 : Fin N241 => decide (a241x4 = w241x5))))).getD h241x3 false = true) → ∀ lpw241 : ℕ → Fin N241 → Prop, lpw241 = (fun (h241x4 : ℕ) (w241x6 : Fin N241) => ∀ w241x7 : Fin N241, lh241 h241x4 w241x7 ↔ w241x7 = w241x6) → ∀ lps241 : Fin N241 → Fin N241 → Prop, lps241 = (fun p241x6 w241x8 : Fin N241 => ∃ h241x5 : ℕ, lpw241 h241x5 w241x8 ∧ ap241 h241x5 p241x6) → ∃ (TL241 TP241 : Finset (Fin N241)) (KB241 KP241 : Finset ℕ) (own241 : ℕ → Fin N241), (∀ j241x9 ∈ KB241 ∪ KP241, cone241 j241x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C241 j241x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ Disjoint KB241 KP241 ∧ (∀ j241x10 ∈ KB241, ∃ p241x7 p241x8 : Fin N241, p241x7 ≠ p241x8 ∧ lvx241 (fun a241x5 : Fin N241 => decide (a241x5 = p241x7)) j241x10 ∧ lvx241 (fun a241x6 : Fin N241 => decide (a241x6 = p241x8)) j241x10) ∧ (∀ j241x11 ∈ KP241, own241 j241x11 ∈ TP241 ∧ ∀ p241x9 : Fin N241, lvx241 (fun a241x7 : Fin N241 => decide (a241x7 = p241x9)) j241x11 → p241x9 = own241 j241x11) ∧ (∀ p241x10 ∈ TP241, ∃ j241x12 ∈ KP241, own241 j241x12 = p241x10) ∧ (∀ p241x11 w241x9 : Fin N241, lps241 p241x11 w241x9 → w241x9 ∈ TL241 ∨ p241x11 ∈ TP241) ∧ ∑ w241x10 : Fin N241, Set.ncard {p241x12 : Fin N241 | lps241 p241x12 w241x10} + TL241.card + Set.ncard {j241x13 : ℕ | cone241 j241x13} ≤ Set.ncard {j241x14 : ℕ | j241x14 < C241.gates.length ∧ (C241.lineDegrees (N241 + N241) (Finset.Ico N241 (N241 + N241))).getD (N241 + N241 + j241x14) 0 = 0} + KB241.card + Set.ncard {js241 : ℕ × ℕ | cone241 js241.1 ∧ js241.2 < 2 ∧ (C241.lineDegrees (N241 + N241) (Finset.range N241)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) 0 = 0 ∧ ∃ w241x11 : Fin N241, lpw241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241.1).inputs.getD js241.2 0) w241x11} + Set.ncard {js241x1 : ℕ × ℕ | cone241 js241x1.1 ∧ js241x1.2 < 2 ∧ mixed241 ((PEqualNP.MetaComplexity.NestedCover.gateAt C241 js241x1.1).inputs.getD js241x1.2 0)} + 1) → (∀ (N250 k250 : ℕ) (I250 : Fin N250 → Fin N250 → Prop) [DecidableRel I250] (C250 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g250 ∈ C250.gates, (g250.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g250.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g250.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N250 + N250) C250) → (∀ j250 < C250.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250 0 = 0) ∨ (∀ h250 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250).inputs, (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250 0 = 0)) → (∀ p250 p250x1 w250 w250x1 : Fin N250, p250 ≠ p250x1 → w250 ≠ w250x1 → I250 p250 w250 → I250 p250x1 w250 → I250 p250 w250x1 → I250 p250x1 w250x1 → False) → (∃ p250x2 w250x2 : Fin N250, I250 p250x2 w250x2) → 1 ≤ k250 → (∀ p250x3 w250x3 : Fin N250, I250 p250x3 w250x3 → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append (fun a250 : Fin N250 => decide (a250 = p250x3)) (fun a250x1 : Fin N250 => decide (a250x1 = w250x3))) = true) → (∀ x250 y250 : Fin N250 → Bool, (Finset.univ.filter (fun l250 : Fin N250 => y250 l250 = true)).card ≤ k250 → (¬ ∃ p250x4 w250x4 : Fin N250, I250 p250x4 w250x4 ∧ x250 p250x4 = true ∧ y250 w250x4 = true) → PEqualNP.MetaComplexity.circuitFun (N250 + N250) C250 (Fin.append x250 y250) = false) → ∀ mixed250 : ℕ → Prop, mixed250 = (fun i250x1 : ℕ => 0 < (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD i250x1 0 ∧ 0 < (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250x1 0) → ∀ cone250 : ℕ → Prop, cone250 = (fun j250x1 : ℕ => j250x1 < C250.gates.length ∧ mixed250 (N250 + N250 + j250x1) ∧ Relation.ReflTransGen (fun a250x2 b250 : ℕ => a250x2 < b250 ∧ ∃ f250 : Fin C250.gates.length, b250 = N250 + N250 + f250.val ∧ a250x2 ∈ (C250.gates.get f250).inputs) (N250 + N250 + j250x1) C250.output) → ∀ gok250 : (Fin N250 → Bool) → ℕ → Prop, gok250 = (fun (x250x1 : Fin N250 → Bool) (j250x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i250x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x2).inputs, (C250.lineDegrees (N250 + N250) (Finset.Ico N250 (N250 + N250))).getD i250x2 0 = 0 ∧ (C250.wires (List.ofFn (Fin.append x250x1 (fun u250 : Fin N250 => false)))).getD i250x2 false = true) → ∀ step250 : (Fin N250 → Bool) → ℕ → ℕ → Prop, step250 = (fun (x250x2 : Fin N250 → Bool) (j250x3 j250x4 : ℕ) => cone250 j250x4 ∧ N250 + N250 + j250x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x4).inputs ∧ gok250 x250x2 j250x4) → ∀ lvx250 : (Fin N250 → Bool) → ℕ → Prop, lvx250 = (fun (x250x3 : Fin N250 → Bool) (j250x5 : ℕ) => cone250 j250x5 ∧ gok250 x250x3 j250x5 ∧ ∃ j250x6 : ℕ, N250 + N250 + j250x6 = C250.output ∧ Relation.ReflTransGen (step250 x250x3) j250x5 j250x6) → ∀ slot250 : ℕ → ℕ → Prop, slot250 = (fun h250x1 j250x7 : ℕ => cone250 j250x7 ∧ h250x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x7).inputs ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD h250x1 0 = 0) → ∀ ap250 : ℕ → Fin N250 → Prop, ap250 = (fun (h250x2 : ℕ) (p250x5 : Fin N250) => ∃ j250x8 : ℕ, slot250 h250x2 j250x8 ∧ lvx250 (fun a250x3 : Fin N250 => decide (a250x3 = p250x5)) j250x8) → ∀ lh250 : ℕ → Fin N250 → Prop, lh250 = (fun (h250x3 : ℕ) (w250x5 : Fin N250) => (C250.wires (List.ofFn (Fin.append (fun u250x1 : Fin N250 => false) (fun a250x4 : Fin N250 => decide (a250x4 = w250x5))))).getD h250x3 false = true) → ∀ lpw250 : ℕ → Fin N250 → Prop, lpw250 = (fun (h250x4 : ℕ) (w250x6 : Fin N250) => ∀ w250x7 : Fin N250, lh250 h250x4 w250x7 ↔ w250x7 = w250x6) → ∀ ppw250 : ℕ → Fin N250 → Prop, ppw250 = (fun (h250x5 : ℕ) (p250x6 : Fin N250) => (∃ w250x8 w250x9 : Fin N250, w250x8 ≠ w250x9 ∧ lh250 h250x5 w250x8 ∧ lh250 h250x5 w250x9) ∧ ∀ p250x7 : Fin N250, ap250 h250x5 p250x7 ↔ p250x7 = p250x6) → ∀ pps250 : Fin N250 → Fin N250 → Prop, pps250 = (fun p250x8 w250x10 : Fin N250 => ∃ h250x6 : ℕ, ppw250 h250x6 p250x8 ∧ lh250 h250x6 w250x10) → (∀ (p250x9 : Fin N250) (h250x7 : ℕ), ppw250 h250x7 p250x9 → ∃ j250x9 : ℕ, cone250 j250x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C250 j250x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ lvx250 (fun a250x5 : Fin N250 => decide (a250x5 = p250x9)) j250x9 ∧ ∀ p250x10 : Fin N250, lvx250 (fun a250x6 : Fin N250 => decide (a250x6 = p250x10)) j250x9 → p250x10 = p250x9) ∧ ∑ p250x11 : Fin N250, min (k250 + 1) (Set.ncard {w250x11 : Fin N250 | pps250 p250x11 w250x11}) ≤ Set.ncard {j250x10 : ℕ | j250x10 < C250.gates.length ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD (N250 + N250 + j250x10) 0 = 0} + Set.ncard {h250x8 : ℕ | ∃ p250x12 : Fin N250, ppw250 h250x8 p250x12} ∧ Set.ncard {js250 : ℕ × ℕ | cone250 js250.1 ∧ js250.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) 0 = 0 ∧ ∃ w250x12 : Fin N250, lpw250 ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250.1).inputs.getD js250.2 0) w250x12} + Set.ncard {h250x9 : ℕ | ∃ p250x13 : Fin N250, ppw250 h250x9 p250x13} ≤ Set.ncard {js250x1 : ℕ × ℕ | cone250 js250x1.1 ∧ js250x1.2 < 2 ∧ (C250.lineDegrees (N250 + N250) (Finset.range N250)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C250 js250x1.1).inputs.getD js250x1.2 0) 0 = 0}) → ∀ (N260 k260 t260 : ℕ) (I260 : Fin N260 → Fin N260 → Prop) [DecidableRel I260] (C260 : PEqualNP.CircuitLowerBounds.Circuit), (∀ p260 p260x1 w260 w260x1 : Fin N260, p260 ≠ p260x1 → w260 ≠ w260x1 → I260 p260 w260 → I260 p260x1 w260 → I260 p260 w260x1 → I260 p260x1 w260x1 → False) → (∃ p260x2 w260x2 : Fin N260, I260 p260x2 w260x2) → 1 ≤ k260 → ((∀ g260 ∈ C260.gates, (g260.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g260.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g260.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N260 + N260) C260) → (∀ j260 < C260.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260 0 = 0) ∨ (∀ h260 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260).inputs, (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260 0 = 0)) → (∀ p260x3 w260x3 : Fin N260, I260 p260x3 w260x3 → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append (fun a260 : Fin N260 => decide (a260 = p260x3)) (fun a260x1 : Fin N260 => decide (a260x1 = w260x3))) = true) → (∀ x260 y260 : Fin N260 → Bool, (Finset.univ.filter (fun l260 : Fin N260 => y260 l260 = true)).card ≤ k260 → (¬ ∃ p260x4 w260x4 : Fin N260, I260 p260x4 w260x4 ∧ x260 p260x4 = true ∧ y260 w260x4 = true) → PEqualNP.MetaComplexity.circuitFun (N260 + N260) C260 (Fin.append x260 y260) = false) → (∀ A260 B260 : Finset (Fin N260), (∀ p260x5 w260x5 : Fin N260, I260 p260x5 w260x5 → p260x5 ∈ A260 ∨ w260x5 ∈ B260) → t260 ≤ A260.card + B260.card) → ∀ mixed260 : ℕ → Prop, mixed260 = (fun i260x1 : ℕ => 0 < (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD i260x1 0 ∧ 0 < (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x1 0) → ∀ cone260 : ℕ → Prop, cone260 = (fun j260x1 : ℕ => j260x1 < C260.gates.length ∧ mixed260 (N260 + N260 + j260x1) ∧ Relation.ReflTransGen (fun a260x2 b260 : ℕ => a260x2 < b260 ∧ ∃ f260 : Fin C260.gates.length, b260 = N260 + N260 + f260.val ∧ a260x2 ∈ (C260.gates.get f260).inputs) (N260 + N260 + j260x1) C260.output) → ∀ gok260 : (Fin N260 → Bool) → ℕ → Prop, gok260 = (fun (x260x1 : Fin N260 → Bool) (j260x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i260x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x2).inputs, (C260.lineDegrees (N260 + N260) (Finset.Ico N260 (N260 + N260))).getD i260x2 0 = 0 ∧ (C260.wires (List.ofFn (Fin.append x260x1 (fun u260 : Fin N260 => false)))).getD i260x2 false = true) → ∀ step260 : (Fin N260 → Bool) → ℕ → ℕ → Prop, step260 = (fun (x260x2 : Fin N260 → Bool) (j260x3 j260x4 : ℕ) => cone260 j260x4 ∧ N260 + N260 + j260x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x4).inputs ∧ gok260 x260x2 j260x4) → ∀ lvx260 : (Fin N260 → Bool) → ℕ → Prop, lvx260 = (fun (x260x3 : Fin N260 → Bool) (j260x5 : ℕ) => cone260 j260x5 ∧ gok260 x260x3 j260x5 ∧ ∃ j260x6 : ℕ, N260 + N260 + j260x6 = C260.output ∧ Relation.ReflTransGen (step260 x260x3) j260x5 j260x6) → ∀ slot260 : ℕ → ℕ → Prop, slot260 = (fun h260x1 j260x7 : ℕ => cone260 j260x7 ∧ h260x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C260 j260x7).inputs ∧ (C260.lineDegrees (N260 + N260) (Finset.range N260)).getD h260x1 0 = 0) → ∀ ap260 : ℕ → Fin N260 → Prop, ap260 = (fun (h260x2 : ℕ) (p260x6 : Fin N260) => ∃ j260x8 : ℕ, slot260 h260x2 j260x8 ∧ lvx260 (fun a260x3 : Fin N260 => decide (a260x3 = p260x6)) j260x8) → ∀ lh260 : ℕ → Fin N260 → Prop, lh260 = (fun (h260x3 : ℕ) (w260x6 : Fin N260) => (C260.wires (List.ofFn (Fin.append (fun u260x1 : Fin N260 => false) (fun a260x4 : Fin N260 => decide (a260x4 = w260x6))))).getD h260x3 false = true) → ∀ lpw260 : ℕ → Fin N260 → Prop, lpw260 = (fun (h260x4 : ℕ) (w260x7 : Fin N260) => ∀ w260x8 : Fin N260, lh260 h260x4 w260x8 ↔ w260x8 = w260x7) → ∀ ppw260 : ℕ → Fin N260 → Prop, ppw260 = (fun (h260x5 : ℕ) (p260x7 : Fin N260) => (∃ w260x9 w260x10 : Fin N260, w260x9 ≠ w260x10 ∧ lh260 h260x5 w260x9 ∧ lh260 h260x5 w260x10) ∧ ∀ p260x8 : Fin N260, ap260 h260x5 p260x8 ↔ p260x8 = p260x7) → ∀ lps260 : Fin N260 → Fin N260 → Prop, lps260 = (fun p260x9 w260x11 : Fin N260 => ∃ h260x6 : ℕ, lpw260 h260x6 w260x11 ∧ ap260 h260x6 p260x9) → ∀ pps260 : Fin N260 → Fin N260 → Prop, pps260 = (fun p260x10 w260x12 : Fin N260 => ∃ h260x7 : ℕ, ppw260 h260x7 p260x10 ∧ lh260 h260x7 w260x12) → ∑ w260x13 : Fin N260, Set.ncard {p260x11 : Fin N260 | lps260 p260x11 w260x13} + ∑ p260x12 : Fin N260, min (k260 + 1) (Set.ncard {w260x14 : Fin N260 | pps260 p260x12 w260x14}) + t260 ≤ C260.size + 1 := by
  intro H230 H231 H241 H250 N k t I instI C hno4 hedge hk hG hKM htrue hfalse hcov mixed hmixed
    cone hcone gok hgok step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps
    pps hpps
  classical
  have hfalse1 : ∀ x y : Fin N → Bool,
      (Finset.univ.filter (fun l : Fin N => y l = true)).card ≤ 1 →
      (¬ ∃ p w : Fin N, I p w ∧ x p = true ∧ y w = true) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C (Fin.append x y) = false :=
    fun x y h1 h2 => hfalse x y (le_trans h1 hk) h2
  have hallpts : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false)) = false :=
    hfalse _ _ (by simp) (by simp)
  have h230 := H230 N C hG hKM hallpts mixed hmixed cone hcone
  have h231 := H231 N I C hG hKM hno4 hedge htrue hfalse1 mixed hmixed cone hcone gok hgok
    step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw lps hlps pps hpps
  have h241 := H241 N I C hG hKM hno4 hedge htrue hfalse1 mixed hmixed cone hcone gok hgok
    step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw lps hlps
  have h250 := H250 N k I C hG hKM hno4 hedge hk htrue hfalse mixed hmixed cone hcone gok hgok
    step hstep lvx hlvx slot hslot ap hap lh hlh lpw hlpw ppw hppw pps hpps
  obtain ⟨TL, TP, KB, KP, own, hKand, hdisj, hKB, hKP, hTPs, hlpsCov, h241i⟩ := h241
  obtain ⟨h250J, h250B, h250S⟩ := h250
  obtain ⟨_, _, _, _, _, hIcov⟩ := h231
  obtain ⟨_, h230e, _⟩ := h230
  have hcone_lt : ∀ j, cone j → j < C.gates.length ∧ mixed (N + N + j) := by
    intro j hj
    rw [hcone] at hj
    exact ⟨hj.1, hj.2.1⟩
  -- the cover
  let PP : Finset (Fin N) := Finset.univ.filter (fun p => ∃ h, ppw h p)
  have ht : t ≤ (TP ∪ PP).card + TL.card := by
    apply hcov
    intro p w hpw
    rcases hIcov p w hpw with h | h
    · rcases hlpsCov p w h with h1 | h1
      · exact Or.inr h1
      · exact Or.inl (Finset.mem_union_left _ h1)
    · refine Or.inl (Finset.mem_union_right _ ?_)
      rw [hpps] at h
      obtain ⟨h0, h1, _⟩ := h
      simp only [PP, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h0, h1⟩
  have hJ : ∀ p ∈ PP, ∃ j, cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      lvx (fun a : Fin N => decide (a = p)) j ∧
      ∀ q : Fin N, lvx (fun a : Fin N => decide (a = q)) j → q = p := by
    intro p hp
    simp only [PP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨h, hh⟩ := hp
    exact h250J p h hh
  choose! fJ hfJ using hJ
  choose! fT hfT1 hfT2 using hTPs
  let f : Fin N → ℕ := fun p => if p ∈ TP then fT p else fJ p
  have hPP : ∀ p ∈ TP ∪ PP, p ∉ TP → p ∈ PP := by
    intro p hp hn
    rcases Finset.mem_union.1 hp with h | h
    · exact absurd h hn
    · exact h
  have hinj : Set.InjOn f ↑(TP ∪ PP) := by
    intro p hp q hq he
    rw [Finset.mem_coe] at hp hq
    simp only [f] at he
    split_ifs at he with h1 h2 h2
    · rw [← hfT2 p h1, ← hfT2 q h2, he]
    · have hq2 := hPP q hq h2
      have hx := (hKP (fT p) (hfT1 p h1)).2 q (by rw [he]; exact (hfJ q hq2).2.2.1)
      rw [hfT2 p h1] at hx
      exact absurd (hx ▸ h1) h2
    · have hp2 := hPP p hp h1
      have hx := (hKP (fT q) (hfT1 q h2)).2 p (by rw [← he]; exact (hfJ p hp2).2.2.1)
      rw [hfT2 q h2] at hx
      exact absurd (hx ▸ h2) h1
    · have hp2 := hPP p hp h1
      have hq2 := hPP q hq h2
      exact ((hfJ p hp2).2.2.2 q (by rw [he]; exact (hfJ q hq2).2.2.1)).symm
  have hdisjK : Disjoint KB ((TP ∪ PP).image f) := by
    rw [Finset.disjoint_left]
    intro j hjB hjI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hjI
    simp only [f] at hjB
    split_ifs at hjB with h1
    · exact Finset.disjoint_left.1 hdisj hjB (hfT1 p h1)
    · have hq := hPP p hp h1
      obtain ⟨p1, p2, hne, hl1, hl2⟩ := hKB _ hjB
      have e1 := (hfJ p hq).2.2.2 p1 hl1
      have e2 := (hfJ p hq).2.2.2 p2 hl2
      exact hne (e1.trans e2.symm)
  have hfinAnd : Set.Finite {j : ℕ | cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} :=
    (Finset.range C.gates.length).finite_toSet.subset
      (fun j hj => Finset.mem_coe.2 (Finset.mem_range.2 (hcone_lt j hj.1).1))
  have hfinOr : Set.Finite {j : ℕ | cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or} :=
    (Finset.range C.gates.length).finite_toSet.subset
      (fun j hj => Finset.mem_coe.2 (Finset.mem_range.2 (hcone_lt j hj.1).1))
  have hfinCone : Set.Finite {j : ℕ | cone j} :=
    (Finset.range C.gates.length).finite_toSet.subset
      (fun j hj => Finset.mem_coe.2 (Finset.mem_range.2 (hcone_lt j hj).1))
  have hsub : (↑(KB ∪ (TP ∪ PP).image f) : Set ℕ) ⊆ {j : ℕ | cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    intro j hj
    rw [Finset.mem_coe, Finset.mem_union] at hj
    rcases hj with hj | hj
    · exact hKand j (Finset.mem_union_left _ hj)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
      simp only [f]
      split_ifs with h1
      · exact hKand _ (Finset.mem_union_right _ (hfT1 p h1))
      · have hq := hPP p hp h1
        exact ⟨(hfJ p hq).1, (hfJ p hq).2.1⟩
  have hcard : KB.card + (TP ∪ PP).card ≤ Set.ncard {j : ℕ | cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [← Finset.card_image_of_injOn hinj, ← Finset.card_union_of_disjoint hdisjK,
      ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub hfinAnd
  have horand : Set.ncard {j : ℕ | cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or} +
      Set.ncard {j : ℕ | cone j ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} ≤
      Set.ncard {j : ℕ | cone j} := by
    have hd : Disjoint {j : ℕ | cone j ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or}
        {j : ℕ | cone j ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
      rw [Set.disjoint_left]
      intro j h1 h2
      have e := h1.2.symm.trans h2.2
      cases e
    rw [← Set.ncard_union_eq hd hfinOr hfinAnd]
    exact Set.ncard_le_ncard (fun j hj => by rcases hj with hj | hj <;> exact hj.1) hfinCone
  -- the three gate classes
  have hne : ∀ g ∈ C.gates, g.inputs ≠ [] := by
    intro g hg he
    have hl := (hG.1 g hg).2
    rw [he] at hl
    simp at hl
  have hdeg := PEqualNP.Outside.L_meta_1954.deg_pos C (N + N) (Finset.range N)
    (Finset.Ico N (N + N)) (by intro i hi; simp only [Finset.mem_range, Finset.mem_Ico]; omega)
    hG.2 hne
  have hparts : Set.ncard {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 = 0} +
      Set.ncard {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 = 0} +
      Set.ncard {j : ℕ | cone j} ≤ C.gates.length := by
    have hf1 : Set.Finite {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 = 0} :=
      (Finset.range C.gates.length).finite_toSet.subset
        (fun j hj => Finset.mem_coe.2 (Finset.mem_range.2 hj.1))
    have hf2 : Set.Finite {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 = 0} :=
      (Finset.range C.gates.length).finite_toSet.subset
        (fun j hj => Finset.mem_coe.2 (Finset.mem_range.2 hj.1))
    have d1 : Disjoint {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 = 0}
        {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 = 0} := by
      rw [Set.disjoint_left]
      intro j h1 h2
      obtain ⟨hj, e1⟩ := h1
      obtain ⟨_, e2⟩ := h2
      have hx := hdeg (N + N + j) (by omega)
      omega
    have d2 : Disjoint ({j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 = 0} ∪
        {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 = 0}) {j : ℕ | cone j} := by
      rw [Set.disjoint_left]
      intro j h1 h2
      have hm := (hcone_lt j h2).2
      simp only [hmixed] at hm
      obtain ⟨m1, m2⟩ := hm
      rcases h1 with h1 | h1
      · obtain ⟨_, e⟩ := h1
        omega
      · obtain ⟨_, e⟩ := h1
        omega
    rw [← Set.ncard_union_eq d1 hf1 hf2, ← Set.ncard_union_eq d2 (hf1.union hf2) hfinCone]
    have hs : ({j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (N + N + j) 0 = 0} ∪
        {j : ℕ | j < C.gates.length ∧
        (C.lineDegrees (N + N) (Finset.range N)).getD (N + N + j) 0 = 0}) ∪ {j : ℕ | cone j} ⊆
        ↑(Finset.range C.gates.length) := by
      intro j hj
      rw [Finset.mem_coe, Finset.mem_range]
      rcases hj with (hj | hj) | hj
      · exact hj.1
      · exact hj.1
      · exact (hcone_lt j hj).1
    have hx := Set.ncard_le_ncard hs (Finset.range C.gates.length).finite_toSet
    rw [Set.ncard_coe_finset, Finset.card_range] at hx
    exact hx
  have hsize : C.size = C.gates.length := rfl
  rw [hsize]
  omega
