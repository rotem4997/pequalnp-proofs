import Mathlib
import PEqualNP.Defs

/- The helper lemmas below (a circuit with s gates of fan-in at most two depends on at most s + 1 inputs) are the ones of our earlier file L_meta_5474.lean. -/
namespace PEqualNP.Outside.L_meta_6114

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

end PEqualNP.Outside.L_meta_6114

theorem PEqualNP.Outside.L_meta_6114 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1), (∃ (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x6 = x4 ∨ x7 = x4) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x8 : Fin x1 → Bool), x3.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → {x9 : Fin x1 | x2.Adj x4 x9}.ncard ≤ x3.size := by
  intro n G C c hex hstar hM hF
  classical
  obtain ⟨S, hS, hval⟩ := PEqualNP.Outside.L_meta_6114.core n C.gates
    (fun g hg => (hM g hg).2) {C.output}
  have hev : ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
      C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
    fun x y hxy => hval x y hxy C.output (by simp)
  have hno : ∀ v : Fin n, C.eval (List.ofFn (fun j => decide (j = v))) ≠ true := by
    intro v h
    obtain ⟨a, b, hab, ha, hb⟩ := (hF _).mp h
    simp only [decide_eq_true_eq] at ha hb
    subst ha
    subst hb
    exact G.irrefl hab
  have hyes : ∀ v, G.Adj c v →
      C.eval (List.ofFn (fun j => decide (j = c ∨ j = v))) = true := by
    intro v hv
    exact (hF _).mpr ⟨c, v, hv, by simp, by simp⟩
  have hN : ∀ v, G.Adj c v → v ∈ S := by
    intro v hv
    by_contra hvS
    have h1 := hev (fun j => decide (j = c ∨ j = v)) (fun j => decide (j = c)) (by
      intro i hi
      have h2 : i ≠ v := fun h => hvS (h ▸ hi)
      simp [h2])
    rw [hyes v hv] at h1
    exact hno c h1.symm
  have hc : c ∈ S := by
    obtain ⟨v, hv⟩ := hex
    by_contra hcS
    have h1 := hev (fun j => decide (j = c ∨ j = v)) (fun j => decide (j = v)) (by
      intro i hi
      have h2 : i ≠ c := fun h => hcS (h ▸ hi)
      simp [h2])
    rw [hyes v hv] at h1
    exact hno v h1.symm
  have hsub : insert c (Finset.univ.filter (fun v => G.Adj c v)) ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | h
    · exact hc
    · exact hN v (Finset.mem_filter.mp h).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at hcard
  have hn : {x9 : Fin n | G.Adj c x9}.ncard =
      (Finset.univ.filter (fun v => G.Adj c v)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [hn]
  simp only [Finset.card_singleton] at hS
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
