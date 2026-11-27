import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4490

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem prefix_foldl : ∀ (gs : List Gate) (l : List Bool), l <+: gs.foldl step l := by
  intro gs
  induction gs with
  | nil => intro l; simp
  | cons g gs ih =>
    intro l
    exact (List.prefix_append l _).trans (ih _)

theorem getD_of_prefix {p q : List Bool} (h : p <+: q) {i : ℕ} (hi : i < p.length) :
    q.getD i false = p.getD i false := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

end PEqualNP.Outside.L_meta_4490

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_4490 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (4 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) →       (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) →         ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)),           x5.size = (3 : ℕ) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               x6.size + (5 : ℕ) = x1.size ∧                 PEqualNP.MetaComplexity.FanInTwo x6 ∧                   (∃! x8 : Fin x6.gates.length, (x6.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧                     ∀ (x8 : Fin (9 : ℕ) → Bool),                       have x9 : List Bool := x5.wires (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ))]);                       x6.eval (x9 ++ [!x9.getD (↑x7) Bool.false]) = x1.eval (List.ofFn x8) := by
  intro x1 hf hnot h9
  obtain ⟨gs, out⟩ := x1
  obtain ⟨i3, i4, hlt, h3, hn3, hn4, honly⟩ := hnot
  have hlen : 4 < gs.length := by
    have := i3.isLt
    simp only at this
    omega
  obtain ⟨g0, g1, g2, g3, g4, R, rfl⟩ : ∃ g0 g1 g2 g3 g4 R, gs = g0 :: g1 :: g2 :: g3 :: g4 :: R := by
    match gs, hlen with
    | g0 :: g1 :: g2 :: g3 :: g4 :: R, _ => exact ⟨g0, g1, g2, g3, g4, R, rfl⟩
  have hg4 : g4.op = GateOp.not := by
    have e : (g0 :: g1 :: g2 :: g3 :: g4 :: R).get i3 = g4 := by
      obtain ⟨v, hv⟩ := i3
      simp only at h3
      subst h3
      rfl
    rw [← e]
    exact hn3
  have h4lt : 4 < i4.val := by
    have : i3.val < i4.val := hlt
    omega
  have hmono : ∀ k : Fin (g0 :: g1 :: g2 :: g3 :: g4 :: R).length, k.val ≠ 4 → k.val ≠ i4.val →
      ((g0 :: g1 :: g2 :: g3 :: g4 :: R).get k).op ≠ GateOp.not := by
    intro k hk1 hk2 h
    rcases honly k h with h' | h'
    · exact hk1 (by rw [h', h3])
    · exact hk2 (by rw [h'])
  have hmo : ∀ (k : Fin (g0 :: g1 :: g2 :: g3 :: g4 :: R).length), k.val ≠ 4 → k.val ≠ i4.val →
      ((g0 :: g1 :: g2 :: g3 :: g4 :: R).get k).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        ((g0 :: g1 :: g2 :: g3 :: g4 :: R).get k).inputs.length ≤ 2 := by
    intro k hk1 hk2
    have hfg := hf _ (List.get_mem _ k)
    have hne := hmono k hk1 hk2
    refine ⟨?_, hfg.2⟩
    have h1 := hfg.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
    tauto
  refine ⟨⟨[g1, g2, g3], 0⟩, ⟨R, out⟩, ⟨min (g4.inputs.headD 13) 13, by omega⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hmo ⟨1, by simp⟩ (by simp) (by simp; omega)
    · exact hmo ⟨2, by simp⟩ (by simp) (by simp; omega)
    · exact hmo ⟨3, by simp⟩ (by simp) (by simp; omega)
  · show R.length + 5 = (g0 :: g1 :: g2 :: g3 :: g4 :: R).length
    simp
  · intro g hg
    exact hf g (by simp [hg])
  · have hi4 : i4.val - 5 < R.length := by
      have := i4.isLt
      simp only [List.length_cons] at this
      omega
    refine ⟨⟨i4.val - 5, hi4⟩, ?_, ?_⟩
    · have e : (g0 :: g1 :: g2 :: g3 :: g4 :: R).get i4 = R.get ⟨i4.val - 5, hi4⟩ := by
        obtain ⟨v, hv⟩ := i4
        simp only at h4lt hi4 ⊢
        obtain ⟨w, rfl⟩ : ∃ w, v = w + 5 := ⟨v - 5, by omega⟩
        simp
      show (R.get ⟨i4.val - 5, hi4⟩).op = GateOp.not
      rw [← e]
      exact hn4
    · intro j hj
      have hj5 : j.val + 5 < (g0 :: g1 :: g2 :: g3 :: g4 :: R).length := by simp
      have e : R.get j = (g0 :: g1 :: g2 :: g3 :: g4 :: R).get ⟨j.val + 5, hj5⟩ := by simp
      rw [e] at hj
      rcases honly _ hj with h' | h'
      · have := congrArg Fin.val h'
        simp only at this
        omega
      · apply Fin.ext
        have := congrArg Fin.val h'
        simp only at this ⊢
        omega
  · intro x8
    have hv0 := h9 x8
    rw [PEqualNP.Outside.L_meta_4490.wires_eq, List.foldl_cons,
      PEqualNP.Outside.L_meta_4490.getD_of_prefix (PEqualNP.Outside.L_meta_4490.prefix_foldl _ _)
        (by simp [PEqualNP.Outside.L_meta_4490.step])] at hv0
    have hstep0 : PEqualNP.Outside.L_meta_4490.step (List.ofFn x8) g0 = List.ofFn x8 ++ [x8 0 || x8 2] := by
      unfold PEqualNP.Outside.L_meta_4490.step at hv0 ⊢
      rw [List.getD_append_right _ _ _ _ (by simp)] at hv0
      simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero] at hv0
      rw [hv0]
    simp only [Circuit.eval, PEqualNP.Outside.L_meta_4490.wires_eq, List.foldl_cons, List.foldl_nil, hstep0]
    congr 1
    set W := PEqualNP.Outside.L_meta_4490.step (PEqualNP.Outside.L_meta_4490.step
      (PEqualNP.Outside.L_meta_4490.step (List.ofFn x8 ++ [x8 0 || x8 2]) g1) g2) g3 with hW
    have hWl : W.length = 13 := by simp [hW, PEqualNP.Outside.L_meta_4490.step]
    congr 1
    show W ++ [!W.getD (min (g4.inputs.headD 13) 13) false] = PEqualNP.Outside.L_meta_4490.step W g4
    unfold PEqualNP.Outside.L_meta_4490.step
    congr 2
    rw [hg4]
    show (!W.getD (min (g4.inputs.headD 13) 13) false) = (!((g4.inputs.map fun i => W.getD i false).headD false))
    congr 1
    rcases g4.inputs with _ | ⟨a, rest⟩
    · simp [List.getD_eq_getElem?_getD, hWl]
    · simp only [List.headD_cons, List.map_cons]
      by_cases ha : a ≤ 13
      · rw [Nat.min_eq_left ha]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
