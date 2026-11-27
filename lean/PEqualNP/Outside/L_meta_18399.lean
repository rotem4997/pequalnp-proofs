import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.CircuitLowerBounds

private def Joined (a b c : List Bool) : Prop :=
  b.length = a.length ∧ c.length = a.length ∧
    ∀ i, c.getD i false = (a.getD i false || b.getD i false)

private theorem joinedInputs {n : ℕ} (a b : Fin n → Bool) :
    Joined (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

private theorem anyJoined {a b c : List Bool} (h : Joined a b c) (inputs : List ℕ) :
    (inputs.map (fun i => c.getD i false)).any id =
    ((inputs.map (fun i => a.getD i false)).any id ||
     (inputs.map (fun i => b.getD i false)).any id) := by
  induction inputs with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    rw [h.2.2 i, ih]
    ac_rfl

private theorem joinedAppend {a b c : List Bool} (h : Joined a b c) (x y : Bool) :
    Joined (a ++ [x]) (b ++ [y]) (c ++ [x || y]) := by
  rcases h with ⟨hb, hc, hw⟩
  refine ⟨by simp [hb], by simp [hc], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ (by simpa [hc] using hi),
        List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by simpa [hb] using hi)]
    exact hw i
  · have hn := Nat.le_of_not_lt hi
    rw [List.getD_append_right _ _ _ _ (by simpa [hc] using hn),
        List.getD_append_right _ _ _ _ hn,
        List.getD_append_right _ _ _ _ (by simpa [hb] using hn), hc, hb]
    cases i - a.length <;> simp

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldJoined (gates : List Gate) (hor : ∀ g ∈ gates, g.op = .or)
    {a b c : List Bool} (h : Joined a b c) :
    Joined (gates.foldl step a) (gates.foldl step b) (gates.foldl step c) := by
  induction gates generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hor q (List.mem_cons_of_mem g hq))
    simp only [step, hor g (List.mem_cons_self), GateOp.eval, anyJoined h]
    exact joinedAppend h _ _

private theorem outputJoined {n : ℕ} (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = .or)
    (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) =
      (C.eval (List.ofFn a) || C.eval (List.ofFn b)) :=
  (foldJoined C.gates hor (joinedInputs a b)).2.2 C.output

end PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18399_aux in
theorem PEqualNP.Outside.L_meta_18399 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (¬∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro m n E C _ hAO correct noAnd
  have hOr : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    rcases hAO.1 g hg with h | h
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
      exact (noAnd ⟨i, (congrArg Gate.op hi).trans h⟩).elim
    · exact h
  have disjoint (u : Fin m) (v : Fin n) : Fin.castAdd n u ≠ Fin.natAdd m v := by
    intro h
    have he := congrArg Fin.val h
    change u.val = m + v.val at he
    have hu := u.isLt
    omega
  have noEdge : ∀ e, e ∉ E := by
    rintro ⟨u, v⟩ hv
    let a : Fin (m + n) → Bool := fun i => decide (i = Fin.castAdd n u)
    let b : Fin (m + n) → Bool := fun i => decide (i = Fin.natAdd m v)
    have ha : C.eval (List.ofFn a) = false := by
      change circuitFun (m + n) C a = false
      rw [correct, decide_eq_false_iff_not]
      rintro ⟨i, j, _, _, hj⟩
      exact disjoint u j ((of_decide_eq_true hj).symm)
    have hb : C.eval (List.ofFn b) = false := by
      change circuitFun (m + n) C b = false
      rw [correct, decide_eq_false_iff_not]
      rintro ⟨i, j, _, hi, _⟩
      exact disjoint i v (of_decide_eq_true hi)
    have hab : C.eval (List.ofFn fun i => a i || b i) = true := by
      change circuitFun (m + n) C (fun i => a i || b i) = true
      rw [correct, decide_eq_true_eq]
      exact ⟨u, v, hv, by simp [a], by simp [b]⟩
    have h := outputJoined C hOr a b
    rw [ha, hb, hab] at h
    contradiction
  have hE : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr noEdge
  subst E
  exact ⟨∅, ∅, by simp, by simp⟩
