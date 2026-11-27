import Mathlib
import PEqualNP.Defs

/- The helper lemmas up to wiresFrom_mono are copied from the checked file L_meta_1018.lean of this repository (Apache-2.0); the ones up to core are from our earlier file L_meta_5474.lean. -/
namespace PEqualNP.Outside.L_meta_6814

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


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
open PEqualNP.GenericRejection

def inp {n : ℕ} (X Y : Finset (Fin n)) : Fin (n + n) → Bool :=
  Fin.append (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))

lemma hinp {n : ℕ} (X Y : Finset (Fin n)) : incidenceInput X Y = List.ofFn (inp X Y) := by
  unfold inp
  rw [List.ofFn_fin_append]
  rfl

lemma hmono {n : ℕ} (C : Circuit) (hM : Monotone2 C) (X X' Y Y' : Finset (Fin n))
    (hX : X ⊆ X') (hY : Y ⊆ Y') (h : C.eval (incidenceInput X Y) = true) :
    C.eval (incidenceInput X' Y') = true := by
  have key : ∀ j : Fin (n + n), inp X Y j = true → inp X' Y' j = true := by
    intro j
    induction j using Fin.addCases with
    | left a =>
      simp only [inp, Fin.append_left, decide_eq_true_eq]
      exact fun h => hX h
    | right b =>
      simp only [inp, Fin.append_right, decide_eq_true_eq]
      exact fun h => hY h
  rw [hinp] at h ⊢
  unfold Circuit.eval at h ⊢
  refine wiresFrom_mono C.gates (fun g hg => by simpa using (hM g hg).1) _ _ (by simp) ?_ _ h
  intro i hi
  by_cases hlt : i < n + n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact key _ hi
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hi
    exact Bool.noConfusion hi

lemma main (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit)
    (hpt : ∀ p : Fin n, ∃ l : Fin n, p ∈ S l) (hne : ∀ l : Fin n, (S l).Nonempty)
    (hM : Monotone2 C) (hR : RightOnIncidentPairs S C)
    (hF : ∀ Y : Finset (Fin n), Y.card ≤ 1 →
      C.eval (incidenceInput (zeroSet S Y) Y) = false) :
    n + n ≤ C.size + 1 := by
  obtain ⟨D, hD, hval⟩ := core (n + n) C.gates (fun g hg => (hM g hg).2) {C.output}
  have hev : ∀ x y : Fin (n + n) → Bool, (∀ i ∈ D, x i = y i) →
      C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
    fun x y hxy => hval x y hxy C.output (by simp)
  have hall : ∀ j : Fin (n + n), j ∈ D := by
    intro j
    induction j using Fin.addCases with
    | left p =>
      by_contra hj
      obtain ⟨l, hl⟩ := hpt p
      have ht := hR l p hl
      have hf : C.eval (incidenceInput (∅ : Finset (Fin n)) {l}) = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have h1 := hmono C hM ∅ (zeroSet S {l}) {l} {l} (Finset.empty_subset _)
          (Finset.Subset.refl _) hc
        rw [hF {l} (by simp)] at h1
        exact Bool.noConfusion h1
      have hEq := hev (inp (n := n) {p} {l}) (inp (n := n) ∅ {l}) (by
        intro i hi
        have hne' : i ≠ Fin.castAdd n p := fun h => hj (h ▸ hi)
        induction i using Fin.addCases with
        | left a =>
          have h2 : a ≠ p := fun h => hne' (by rw [h])
          simp only [inp, Fin.append_left]
          simp [h2]
        | right b => simp only [inp, Fin.append_right])
      rw [← hinp, ← hinp, ht, hf] at hEq
      exact Bool.noConfusion hEq
    | right l =>
      by_contra hj
      obtain ⟨p, hp⟩ := hne l
      have ht := hR l p hp
      have hf : C.eval (incidenceInput {p} (∅ : Finset (Fin n))) = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have h1 := hmono C hM {p} (zeroSet S ∅) ∅ ∅ (by intro a _; simp [zeroSet])
          (Finset.Subset.refl _) hc
        rw [hF ∅ (by simp)] at h1
        exact Bool.noConfusion h1
      have hEq := hev (inp (n := n) {p} {l}) (inp (n := n) {p} ∅) (by
        intro i hi
        have hne' : i ≠ Fin.natAdd n l := fun h => hj (h ▸ hi)
        induction i using Fin.addCases with
        | left a => simp only [inp, Fin.append_left]
        | right b =>
          have h2 : b ≠ l := fun h => hne' (by rw [h])
          simp only [inp, Fin.append_right]
          simp [h2])
      rw [← hinp, ← hinp, ht, hf] at hEq
      exact Bool.noConfusion hEq
  have hu : D = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [hu] at hD
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hD
  unfold Circuit.size
  omega

end PEqualNP.Outside.L_meta_6814

theorem PEqualNP.Outside.L_meta_6814 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 : Fin x1), ∃ (x5 : Fin x1), x4 ∈ x2 x5) → (∀ (x5 : Fin x1), (x2 x5).Nonempty) → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.GenericRejection.RightOnIncidentPairs x2 x3 → (∀ (x8 : Finset (Fin x1)), x8.card ≤ (1 : ℕ) → x3.eval (PEqualNP.GenericRejection.incidenceInput (PEqualNP.GenericRejection.zeroSet x2 x8) x8) = Bool.false) → x1 + x1 ≤ x3.size + (1 : ℕ) := by
  intro n S C hpt hne hM hR hF
  exact PEqualNP.Outside.L_meta_6814.main n S C hpt hne hM hR hF
