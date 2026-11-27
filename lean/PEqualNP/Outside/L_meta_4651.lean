import Mathlib
import PEqualNP.Defs


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4651

def LeW (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

def GLe (g h : Gate) : Prop :=
  ∀ a b : List Bool, LeW a b →
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    h.op.eval (h.inputs.map fun i => b.getD i false) = true

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (a : List Bool) (u : Bool) (i : ℕ) :
    (a ++ [u]).getD i false =
      if i < a.length then a.getD i false else if i = a.length then u else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_append_right (by omega)]
    have hk : i - a.length ≠ 0 := by omega
    simp [hk]

theorem leW_snoc {a b : List Bool} {u v : Bool} (hab : LeW a b) (huv : u = true → v = true) :
    LeW (a ++ [u]) (b ++ [v]) := by
  refine ⟨by simp [hab.1], fun i hi => ?_⟩
  rw [getD_snoc] at hi ⊢
  rw [← hab.1]
  split_ifs at hi ⊢ with h1 h2
  · exact hab.2 i hi
  · exact huv hi

theorem foldl_le : ∀ (gs hs : List Gate), List.Forall₂ GLe gs hs → ∀ a b : List Bool, LeW a b →
    LeW (gs.foldl step a) (hs.foldl step b)
  | [], [], _, _, _, h => h
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | _ :: gs, _ :: hs, List.Forall₂.cons hgh hrest, a, b, hab =>
      foldl_le gs hs hrest _ _ (leW_snoc hab (hgh a b hab))

theorem eval_le (D E : Circuit) (hout : D.output = E.output)
    (hg : List.Forall₂ GLe D.gates E.gates) (x y : List Bool) (hxy : LeW x y) :
    D.eval x = true → E.eval y = true := by
  intro h
  have key := (foldl_le D.gates E.gates hg x y hxy).2 D.output
  unfold Circuit.eval Circuit.wires at *
  rw [← hout]
  exact key h

theorem gle_self (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) : GLe g g := by
  intro a b hab hx
  rcases hop with h | h
  · rw [h] at hx ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx ⊢
    intro i hi
    exact hab.2 i (hx i hi)
  · rw [Set.mem_singleton_iff] at h
    rw [h] at hx ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id, exists_exists_and_eq_and] at hx ⊢
    obtain ⟨i, hi, ht⟩ := hx
    exact ⟨i, hi, hab.2 i ht⟩

theorem gle_pass (g : Gate) (w : ℕ) (hop : g.op = GateOp.or) (hw : w ∈ g.inputs) :
    GLe ⟨GateOp.and, [w]⟩ g := by
  intro a b hab hx
  rw [hop]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
    Bool.and_true] at hx
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id, exists_exists_and_eq_and]
  exact ⟨w, hw, hab.2 w hx⟩

theorem forall2_set (l : List Gate) (j : ℕ) (g0 : Gate) (hj : j < l.length)
    (hall : ∀ g ∈ l, GLe g g) (hj0 : GLe g0 l[j]) :
    List.Forall₂ GLe (l.set j g0) l := by
  rw [List.forall₂_iff_get]
  refine ⟨List.length_set .., fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_set]
  split_ifs with hij
  · subst hij
    exact hj0
  · exact hall _ (List.getElem_mem h2)

theorem mono_set (C : Circuit) (j w : ℕ) (hm : Monotone2 C) :
    Monotone2 ⟨C.gates.set j ⟨GateOp.and, [w]⟩, C.output⟩ := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with h | h
  · exact hm g h
  · subst h
    exact ⟨Or.inl rfl, by simp⟩

theorem leW_ofFn {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) :
    LeW (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun i hi => ?_⟩
  by_cases hin : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin] at hi ⊢
    simpa using h ⟨i, hin⟩ (by simpa using hi)
  · simp [List.getD_eq_getElem?_getD, hin] at hi

theorem orcount_lt (C : Circuit) (j : Fin C.gates.length) (w : ℕ)
    (hop : (C.gates.get j).op = GateOp.or) :
    {i : Fin (C.gates.set j ⟨GateOp.and, [w]⟩).length |
        ((C.gates.set j ⟨GateOp.and, [w]⟩).get i).op = GateOp.or}.ncard <
      {i : Fin C.gates.length | (C.gates.get i).op = GateOp.or}.ncard := by
  have hL : (C.gates.set j ⟨GateOp.and, [w]⟩).length = C.gates.length := List.length_set ..
  rw [← Set.ncard_image_of_injective _ (Fin.cast_injective hL)]
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  rw [Set.ssubset_iff_of_subset]
  · refine ⟨j, hop, ?_⟩
    rintro ⟨i, hi, hij⟩
    have hv : (i : ℕ) = j := by simpa using congrArg Fin.val hij
    simp only [Set.mem_ofPred_eq, List.get_eq_getElem, List.getElem_set, hv, ite_true] at hi
    cases hi
  · rintro _ ⟨i, hi, rfl⟩
    have hne : (j : ℕ) ≠ i := by
      intro h
      simp only [Set.mem_ofPred_eq, List.get_eq_getElem, List.getElem_set, h, ite_true] at hi
      cases hi
    simp only [Set.mem_ofPred_eq, List.get_eq_getElem, List.getElem_set, hne, ite_false] at hi ⊢
    simpa using hi

end PEqualNP.Outside.L_meta_4651

open PEqualNP.Outside.L_meta_4651

theorem PEqualNP.Outside.L_meta_4651 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => {x2 : Fin x1.gates.length | (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) => { gates := x2.gates.set x3 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4] : PEqualNP.CircuitLowerBounds.Gate }, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin x4.gates.length) (x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x4 →     (x4.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →       x6 ∈ (x4.gates.get x5).inputs →         have x10 : PEqualNP.CircuitLowerBounds.Circuit := x2 x4 (↑x5) x6;         PEqualNP.MetaComplexity.Monotone2 x10 ∧ x1 x10 < x1 x4 ∧ (∀ (x11 : Fin x3 → Bool), x10.eval (List.ofFn x11) = Bool.true → x4.eval (List.ofFn x11) = Bool.true) ∧ ∀ (x11 x12 : Fin x3 → Bool), (∀ (x13 : Fin x3), x11 x13 = Bool.true → x12 x13 = Bool.true) → x10.eval (List.ofFn x11) = Bool.true → x10.eval (List.ofFn x12) = Bool.true := by
  dsimp only
  intro n C j w hm hop hw
  have hC' := mono_set C j w hm
  have hself : ∀ g ∈ C.gates, GLe g g := fun g hg => gle_self g (hm g hg).1
  have hrel : List.Forall₂ GLe (C.gates.set j ⟨GateOp.and, [w]⟩) C.gates :=
    forall2_set C.gates j _ j.isLt hself (by simpa [List.get_eq_getElem] using gle_pass _ w hop hw)
  have hself' : List.Forall₂ GLe (C.gates.set j ⟨GateOp.and, [w]⟩)
      (C.gates.set j ⟨GateOp.and, [w]⟩) :=
    List.forall₂_same.2 fun g hg => gle_self g (hC' g hg).1
  refine ⟨hC', orcount_lt C j w hop, ?_, ?_⟩
  · intro x hx
    exact eval_le ⟨C.gates.set j ⟨GateOp.and, [w]⟩, C.output⟩ C rfl hrel _ _ ⟨rfl, fun _ h => h⟩ hx
  · intro x y hxy hx
    exact eval_le ⟨_, C.output⟩ ⟨_, C.output⟩ rfl hself' _ _ (leW_ofFn x y hxy) hx
