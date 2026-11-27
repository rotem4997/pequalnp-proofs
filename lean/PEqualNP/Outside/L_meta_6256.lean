import Mathlib
import PEqualNP.Defs

/- The helper lemmas below (a circuit with s gates of fan-in at most two depends on at most s + 1 inputs) are the ones of our earlier file L_meta_5474.lean. -/
namespace PEqualNP.Outside.L_meta_6256

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step of the root model: append the value of the next gate.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepWire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepWire
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepWire w g) (by simp [stepWire]; omega), step_getD, if_pos hi]

lemma foldl_take (gs : List Gate) (w : List Bool) (k r : ℕ) (hr : r < w.length + k) :
    (gs.foldl stepWire w).getD r false = ((gs.take k).foldl stepWire w).getD r false := by
  by_cases hk : k ≤ gs.length
  · conv_lhs => rw [← List.take_append_drop k gs, List.foldl_append]
    apply foldl_getD_lt
    rw [foldl_len, List.length_take, min_eq_left hk]
    exact hr
  · rw [List.take_of_length_le (by omega)]

-- The values of a set W of wires are determined by at most |W| + (number of gates) inputs.
lemma core (n : ℕ) (gs : List Gate) (h2 : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, ∃ S : Finset (Fin n), S.card ≤ W.card + gs.length ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → ∀ w ∈ W,
        (gs.foldl stepWire (List.ofFn x)).getD w false =
          (gs.foldl stepWire (List.ofFn y)).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W
    refine ⟨Finset.univ.filter (fun i : Fin n => i.val ∈ W), ?_, ?_⟩
    · simp only [List.length_nil, add_zero]
      apply Finset.card_le_card_of_injOn (fun i => i.val)
      · intro i hi
        simpa using hi
      · intro i _ j _ h
        exact Fin.ext h
    · intro x y hxy w hw
      simp only [List.foldl_nil, List.getD_eq_getElem?_getD]
      by_cases hwn : w < n
      · have hx : (List.ofFn x)[w]? = some (x ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]
          simp
        have hy : (List.ofFn y)[w]? = some (y ⟨w, hwn⟩) := by
          rw [List.getElem?_eq_getElem (by simpa using hwn)]
          simp
        rw [hx, hy]
        simp only [Option.getD_some]
        exact hxy ⟨w, hwn⟩ (by simp [hw])
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  | append_singleton gs g ih =>
    intro W
    have h2' : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => h2 g' (by simp [hg'])
    have hg : g.inputs.length ≤ 2 := h2 g (by simp)
    have key : ∀ (S : Finset (Fin n)) (W' : Finset ℕ),
        (∀ w ∈ W, w < n + gs.length → w ∈ W') →
        (n + gs.length ∈ W → ∀ k ∈ g.inputs, k ∈ W') →
        (∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → ∀ w ∈ W',
          (gs.foldl stepWire (List.ofFn x)).getD w false =
            (gs.foldl stepWire (List.ofFn y)).getD w false) →
        ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → ∀ w ∈ W,
          ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false =
            ((gs ++ [g]).foldl stepWire (List.ofFn y)).getD w false := by
      intro S W' hlow hin hval x y hxy w hw
      have hv := hval x y hxy
      have hlx := foldl_len gs (List.ofFn x)
      have hly := foldl_len gs (List.ofFn y)
      simp only [List.length_ofFn] at hlx hly
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [step_getD, step_getD, hlx, hly]
      split_ifs with h1 h3
      · exact hv w (hlow w hw h1)
      · subst h3
        congr 1
        apply List.map_congr_left
        intro k hk
        exact hv k (hin hw k hk)
      · rfl
    by_cases hin : n + gs.length ∈ W
    · obtain ⟨S, hS, hval⟩ := ih h2' (W.erase (n + gs.length) ∪ g.inputs.toFinset)
      refine ⟨S, ?_, key S _ ?_ ?_ hval⟩
      · have h1 : (W.erase (n + gs.length) ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
          refine (Finset.card_union_le _ _).trans ?_
          rw [Finset.card_erase_of_mem hin]
          have := List.toFinset_card_le g.inputs
          omega
        have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hin⟩
        simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw hlt
        simp only [Finset.mem_union, Finset.mem_erase]
        exact Or.inl ⟨by omega, hw⟩
      · intro _ k hk
        simp [hk]
    · obtain ⟨S, hS, hval⟩ := ih h2' W
      refine ⟨S, ?_, key S W ?_ ?_ hval⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro w hw _
        exact hw
      · intro h
        exact absurd h hin

end PEqualNP.Outside.L_meta_6256

theorem PEqualNP.Outside.L_meta_6256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1 × Fin x1)), PEqualNP.TopForm.IsAO2 (x1 + x1) x2 → (∀ (x5 : Fin (x1 + x1)), (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x6 : Fin (x1 + x1)) => Decidable.decide (x6 = x5)) = Bool.false) → (∀ x6 ∈ x3, (PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 fun (x8 : Fin (x1 + x1)) => Decidable.decide (x8 = Fin.castAdd x1 x6.1 ∨ x8 = Fin.natAdd x1 x6.2)) = Bool.true) → (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card ≤ x2.size + (1 : ℕ) := by
  intro n C E hAO hno hyes
  classical
  obtain ⟨S, hS, hval⟩ := PEqualNP.Outside.L_meta_6256.core (n + n) C.gates
    (fun g hg => le_of_eq (hAO.2.2 g hg)) {C.output}
  have hev : ∀ x y : Fin (n + n) → Bool, (∀ i ∈ S, x i = y i) →
      PEqualNP.MetaComplexity.circuitFun (n + n) C x =
        PEqualNP.MetaComplexity.circuitFun (n + n) C y :=
    fun x y hxy => hval x y hxy C.output (by simp)
  have hL : ∀ e ∈ E, Fin.castAdd n e.1 ∈ S := by
    intro e he
    by_contra hS'
    have h1 := hev (fun j => decide (j = Fin.castAdd n e.1 ∨ j = Fin.natAdd n e.2))
      (fun j => decide (j = Fin.natAdd n e.2)) (by
        intro i hi
        have h2 : i ≠ Fin.castAdd n e.1 := fun h => hS' (h ▸ hi)
        exact decide_eq_decide.mpr ⟨fun h => h.resolve_left h2, Or.inr⟩)
    rw [hyes e he, hno] at h1
    exact Bool.noConfusion h1
  have hR : ∀ e ∈ E, Fin.natAdd n e.2 ∈ S := by
    intro e he
    by_contra hS'
    have h1 := hev (fun j => decide (j = Fin.castAdd n e.1 ∨ j = Fin.natAdd n e.2))
      (fun j => decide (j = Fin.castAdd n e.1)) (by
        intro i hi
        have h2 : i ≠ Fin.natAdd n e.2 := fun h => hS' (h ▸ hi)
        exact decide_eq_decide.mpr ⟨fun h => h.resolve_right h2, Or.inl⟩)
    rw [hyes e he, hno] at h1
    exact Bool.noConfusion h1
  have hsub : (Finset.image Prod.fst E).image (Fin.castAdd n) ∪
      (Finset.image Prod.snd E).image (Fin.natAdd n) ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact hL e he
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      exact hR e he
  have hdisj : Disjoint ((Finset.image Prod.fst E).image (Fin.castAdd n))
      ((Finset.image Prod.snd E).image (Fin.natAdd n)) := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h2
    have := congrArg Fin.val hb
    simp only [Fin.val_natAdd, Fin.val_castAdd] at this
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (Fin.castAdd_injective n n),
    Finset.card_image_of_injective _ (Fin.natAdd_injective n n)] at hcard
  simp only [Finset.card_singleton] at hS
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
