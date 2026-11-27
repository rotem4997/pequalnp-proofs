import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6893

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem cf_mono {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true := by
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  unfold PEqualNP.MetaComplexity.circuitFun at h ⊢
  rw [eval_eq] at h ⊢
  refine mono C.gates _ _ (by simp) hg ?_ C.output h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

end PEqualNP.Outside.L_meta_6893

open PEqualNP.Outside.L_meta_6893 in
theorem PEqualNP.Outside.L_meta_6893 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → PEqualNP.MetaComplexity.circuitFun x1 x4 (PEqualNP.EdgeOwnership.pairInput x6 x7) = Bool.true) → (∀ (x7 : Finset (Fin x1)), Maximal (fun (x8 : Finset (Fin x1)) => x2.IsIndepSet ↑x8) x7 → (PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x9 : Fin x1) => Decidable.decide (x9 ∈ x7)) = Bool.false) → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  intro n G _ C hC hE hI
  funext x
  by_cases hx : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hu, hv⟩ := hx
    have hg : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨u, v, huv, hu, hv⟩
    rw [hg]
    refine cf_mono C hC _ x ?_ (hE u v huv)
    intro w hw
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  · have hg : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false := by
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨by simp, hx⟩
    rw [hg]
    let S : Finset (Fin n) := Finset.univ.filter fun t => x t = true
    have hS : G.IsIndepSet (↑S : Set (Fin n)) := by
      intro u hu v hv _ hadj
      have hu' : x u = true := (Finset.mem_filter.1 (Finset.mem_coe.1 hu)).2
      have hv' : x v = true := (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
      exact hx ⟨u, v, hadj, hu', hv'⟩
    obtain ⟨M, hSM, hmax⟩ := Finite.exists_le_maximal
      (p := fun T : Finset (Fin n) => G.IsIndepSet (↑T : Set (Fin n))) hS
    have hM := hI M hmax
    by_contra hne
    have ht : PEqualNP.MetaComplexity.circuitFun n C x = true := by
      simpa using hne
    have := cf_mono C hC x (fun t => decide (t ∈ M)) (fun v hv => by
      have : v ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩
      simpa using hSM this) ht
    rw [hM] at this
    exact absurd this (by decide)
