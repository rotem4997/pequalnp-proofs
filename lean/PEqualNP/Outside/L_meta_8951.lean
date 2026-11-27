import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8951

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




theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8951

theorem PEqualNP.Outside.L_meta_8951 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → (¬∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[(1 : ℕ)]? = Option.some x10) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  intro a b E C X5 _ hAO hF _ hno
  classical
  have hlen : C.gates.length ≤ 1 := by
    by_contra h
    exact hno ⟨C.gates[1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hsz : C.size = C.gates.length := rfl
  rcases E.eq_empty_or_nonempty with rfl | ⟨e0, he0⟩
  · exact ⟨∅, ∅, by simp, by simp⟩
  have ev : ∀ x, PEqualNP.MetaComplexity.circuitFun (a + b) C x = (PEqualNP.Outside.L_meta_8951.run C.gates (List.ofFn x)).getD C.output false := fun _ => rfl
  let pr : Fin a × Fin b → Fin (a + b) → Bool := fun e i => decide (i = Fin.castAdd b e.1 ∨ i = Fin.natAdd a e.2)
  have fpr : ∀ e ∈ E, PEqualNP.MetaComplexity.circuitFun (a + b) C (pr e) = true := by
    intro e he
    rw [hF, decide_eq_true_eq]
    exact ⟨e, he, by simp [pr], by simp [pr]⟩
  have hne : ∀ (p : Fin a) (l : Fin b), Fin.castAdd b p ≠ Fin.natAdd a l := by
    intro p l e
    have := congrArg Fin.val e
    simp at this
    have := p.isLt
    omega
  have f1 : ∀ w : Fin (a + b), PEqualNP.MetaComplexity.circuitFun (a + b) C (fun i => decide (i = w)) = false := by
    intro w
    rw [hF, decide_eq_false_iff_not]
    rintro ⟨e, _, h1, h2⟩
    have h1 : Fin.castAdd b e.1 = w := by simpa using h1
    have h2 : Fin.natAdd a e.2 = w := by simpa using h2
    exact hne _ _ (h1.trans h2.symm)
  have inp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin (a + b) → Bool) (w : ℕ) (hw : w < a + b), (PEqualNP.Outside.L_meta_8951.run gs (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro gs x w hw
    rw [PEqualNP.Outside.L_meta_8951.run_input _ _ _ (by rw [List.length_ofFn]; exact hw), List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hw), List.getElem_ofFn]
  have out1 : ¬ C.output < a + b := by
    intro h
    have h1 := f1 ⟨C.output, h⟩
    rw [ev, inp _ _ _ h] at h1
    simp at h1
  have out2 : C.output < a + b + C.gates.length := by
    by_contra h
    have h1 := fpr e0 he0
    rw [ev, List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_8951.run_length, List.length_ofFn]; omega)] at h1
    cases h1
  have hone : C.gates.length = 1 := by omega
  have ho : C.output = a + b + 0 := by omega
  obtain ⟨hop, hrb, hl2⟩ := hAO
  have h0 : 0 < C.gates.length := by omega
  obtain ⟨u, v, huv⟩ := List.length_eq_two.1 (hl2 _ (List.getElem_mem h0))
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C 0 = C.gates[0] := by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, h0]
  have hr := hrb 0 h0
  rw [hga, huv] at hr
  have hu : u < a + b := by simpa using hr u (by simp)
  have hv : v < a + b := by simpa using hr v (by simp)
  have val : ∀ x : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C x = C.gates[0].op.eval [x ⟨u, hu⟩, x ⟨v, hv⟩] := by
    intro x
    rw [ev, ho]
    have h := PEqualNP.Outside.L_meta_8951.run_gate C.gates (List.ofFn x) 0 h0
    rw [List.length_ofFn, huv] at h
    simp only [List.map_cons, List.map_nil, if_pos (show u < a + b + 0 from hu), if_pos (show v < a + b + 0 from hv), inp _ _ _ hu, inp _ _ _ hv] at h
    exact h
  have hand : C.gates[0].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    rcases hop _ (List.getElem_mem h0) with h | h
    · exact h
    · exfalso
      have h1 := f1 ⟨u, hu⟩
      rw [val, h] at h1
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at h1
  have hne2 : u ≠ v := by
    rintro rfl
    have h1 := f1 ⟨u, hu⟩
    rw [val, hand] at h1
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at h1
  have key : ∀ e ∈ E, ((⟨u, hu⟩ : Fin (a + b)) = Fin.castAdd b e.1 ∧ (⟨v, hv⟩ : Fin (a + b)) = Fin.natAdd a e.2) ∨ ((⟨v, hv⟩ : Fin (a + b)) = Fin.castAdd b e.1 ∧ (⟨u, hu⟩ : Fin (a + b)) = Fin.natAdd a e.2) := by
    intro e he
    have h1 := fpr e he
    rw [val, hand] at h1
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id, Bool.and_eq_true, pr, decide_eq_true_eq] at h1
    obtain ⟨h1 | h1, h2 | h2⟩ := h1
    · exact absurd (congrArg Fin.val (h1.trans h2.symm)) hne2
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact absurd (congrArg Fin.val (h1.trans h2.symm)) hne2
  have hall : ∀ e ∈ E, e = e0 := by
    intro e he
    have c1 : ∀ p p' : Fin a, Fin.castAdd b p = Fin.castAdd b p' → p = p' := fun p p' h => Fin.ext (by simpa using congrArg Fin.val h)
    have c2 : ∀ p p' : Fin b, Fin.natAdd a p = Fin.natAdd a p' → p = p' := fun p p' h => Fin.ext (by simpa using congrArg Fin.val h)
    rcases key e he with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases key e0 he0 with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact Prod.ext (c1 _ _ (a1.symm.trans b1)) (c2 _ _ (a2.symm.trans b2))
    · exact absurd (a1.symm.trans b2) (hne _ _)
    · exact absurd (b1.symm.trans a2) (hne _ _)
    · exact Prod.ext (c1 _ _ (a1.symm.trans b1)) (c2 _ _ (a2.symm.trans b2))
  have hE : E = {e0} := Finset.eq_singleton_iff_unique_mem.2 ⟨he0, hall⟩
  refine ⟨{e0.1}, ∅, fun e he => Or.inl ?_, ?_⟩
  · rw [hall e he]; simp
  · rw [hE]
    simp only [Finset.card_singleton, Finset.card_empty]
    omega
