import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6045

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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



theorem gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

theorem veq (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (o : GateOp)
    (s t : ℕ) (e : gs[j] = ⟨o, [s, t]⟩) (hs : s < n + j) (ht : t < n + j) :
    (run gs (List.ofFn x)).getD (n + j) false = o.eval [(run gs (List.ofFn x)).getD s false,
      (run gs (List.ofFn x)).getD t false] := by
  have := run_gate gs (List.ofFn x) j hj
  rw [List.length_ofFn, e] at this
  rw [this]
  simp [hs, ht]

theorem gate_eta {g : Gate} {o : GateOp} {l : List ℕ} (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  cases g; cases h1; cases h2; rfl


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6045

theorem PEqualNP.Outside.L_meta_6045 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Bool) (x4 : Fin x1) (x5 : ℕ),   have x6 : Fin x1 → Bool := Function.update x3 x4 Bool.true;   have x7 : ℕ → ℕ → Prop := fun (x7 x8 : ℕ) => ∃ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) (x11 : ℕ), x8 = x1 + x9 ∧ x2.gates[x9]? = Option.some x10 ∧ (x10.inputs = [x7, x11] ∨ x10.inputs = [x11, x7]) ∧ (x10.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.ReadTwo.wval x2 x3 x11 = Bool.true);   PEqualNP.TopForm.IsAO2 x1 x2 → PEqualNP.ReadTwo.wval x2 x6 x5 = Bool.true → PEqualNP.ReadTwo.wval x2 x3 x5 = Bool.false → Relation.ReflTransGen x7 (↑x4) x5 ∨ ∃ x11 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs, PEqualNP.ReadTwo.wval x2 x6 x12 = Bool.true ∧ PEqualNP.ReadTwo.wval x2 x3 x12 = Bool.false) ∧ Relation.ReflTransGen x7 (x1 + x11) x5 := by
  intro n C x v w
  intro y E hC hy hx
  let V : (Fin n → Bool) → ℕ → Bool := fun z w => (PEqualNP.Outside.L_meta_6045.run C.gates (List.ofFn z)).getD w false
  have key : ∀ w, V y w = true → V x w = false →
      Relation.ReflTransGen E (v : ℕ) w ∨ ∃ g < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs, V y i = true ∧ V x i = false) ∧
        Relation.ReflTransGen E (n + g) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hy hx
      by_cases h9 : w < n
      · left
        have e1 : V y w = y ⟨w, h9⟩ := by
          simp only [V]
          rw [PEqualNP.Outside.L_meta_6045.run_input _ _ _ (by simpa using h9)]
          exact PEqualNP.Outside.L_meta_6045.gD y ⟨w, h9⟩
        have e2 : V x w = x ⟨w, h9⟩ := by
          simp only [V]
          rw [PEqualNP.Outside.L_meta_6045.run_input _ _ _ (by simpa using h9)]
          exact PEqualNP.Outside.L_meta_6045.gD x ⟨w, h9⟩
        have : (⟨w, h9⟩ : Fin n) = v := by
          by_contra hne
          rw [e1] at hy
          rw [e2] at hx
          have hy' : y ⟨w, h9⟩ = x ⟨w, h9⟩ := Function.update_of_ne hne _ _
          rw [hy', hx] at hy
          cases hy
        rw [← this]
      · by_cases h8 : w < n + C.gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < C.gates.length := by omega
          obtain ⟨g1, g2, g3, g4, hop⟩ := PEqualNP.Outside.L_meta_6045.gate2 hC hj
          have hsome : C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
            rw [← g1]; exact List.getElem?_eq_getElem hj
          set a := PEqualNP.TopForm.opnd C j 0
          set b := PEqualNP.TopForm.opnd C j 1
          have ext : ∀ c d, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, d] ∨
              (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [d, c] →
              ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
                (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ V x d = true) →
              c < n + j → V y c = true → V x c = false →
              Relation.ReflTransGen E (v : ℕ) (n + j) ∨ ∃ g < C.gates.length,
                (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
                (∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs, V y i = true ∧ V x i = false) ∧
                Relation.ReflTransGen E (n + g) (n + j) := by
            intro c d hin hop' hc h1 h2
            have edge : E c (n + j) := ⟨j, _, d, rfl, hsome, hin, hop'⟩
            rcases ih c hc h1 h2 with h | ⟨g, hg, h3, h4, h5⟩
            · exact Or.inl (h.tail edge)
            · exact Or.inr ⟨g, hg, h3, h4, h5.tail edge⟩
          rcases hop with ho | ho
          · have vy := PEqualNP.Outside.L_meta_6045.veq n C.gates y j hj _ _ _ (g1.trans (PEqualNP.Outside.L_meta_6045.gate_eta ho g2)) g3 g4
            have vx := PEqualNP.Outside.L_meta_6045.veq n C.gates x j hj _ _ _ (g1.trans (PEqualNP.Outside.L_meta_6045.gate_eta ho g2)) g3 g4
            have vy' : V y (n + j) = (V y a && V y b) := by simpa [V, PEqualNP.CircuitLowerBounds.GateOp.eval] using vy
            have vx' : V x (n + j) = (V x a && V x b) := by simpa [V, PEqualNP.CircuitLowerBounds.GateOp.eval] using vx
            rw [vy', Bool.and_eq_true] at hy
            rw [vx'] at hx
            cases ha : V x a with
            | true =>
              rw [ha, Bool.true_and] at hx
              exact ext b a (Or.inr g2) (Or.inr ⟨ho, ha⟩) g4 hy.2 hx
            | false =>
              cases hb : V x b with
              | true => exact ext a b (Or.inl g2) (Or.inr ⟨ho, hb⟩) g3 hy.1 ha
              | false =>
                right
                refine ⟨j, hj, ho, ?_, Relation.ReflTransGen.refl⟩
                intro i hi
                rw [g2] at hi
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact ⟨hy.1, ha⟩
                · exact ⟨hy.2, hb⟩
          · have vy := PEqualNP.Outside.L_meta_6045.veq n C.gates y j hj _ _ _ (g1.trans (PEqualNP.Outside.L_meta_6045.gate_eta ho g2)) g3 g4
            have vx := PEqualNP.Outside.L_meta_6045.veq n C.gates x j hj _ _ _ (g1.trans (PEqualNP.Outside.L_meta_6045.gate_eta ho g2)) g3 g4
            have vy' : V y (n + j) = (V y a || V y b) := by simpa [V, PEqualNP.CircuitLowerBounds.GateOp.eval] using vy
            have vx' : V x (n + j) = (V x a || V x b) := by simpa [V, PEqualNP.CircuitLowerBounds.GateOp.eval] using vx
            rw [vy', Bool.or_eq_true] at hy
            rw [vx', Bool.or_eq_false_iff] at hx
            rcases hy with hy | hy
            · exact ext a b (Or.inl g2) (Or.inl ho) g3 hy hx.1
            · exact ext b a (Or.inr g2) (Or.inl ho) g4 hy hx.2
        · simp only [V] at hy
          rw [List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_6045.run_length]; simp; omega)] at hy
          cases hy
  exact key w hy hx
