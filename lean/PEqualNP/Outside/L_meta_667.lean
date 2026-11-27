import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_667_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

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

-- PG(2, 3) finite geometry
def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

lemma card_line (w : Fin 13) : (line w).card = 4 := by
  revert w; decide

lemma card_inter_line (w₁ w₂ : Fin 13) (h : w₁ ≠ w₂) : (line w₁ ∩ line w₂).card = 1 := by
  revert w₁ w₂ h; decide

lemma line_eq_of_subset_two {S : Finset (Fin 13)} {w₁ w₂ : Fin 13}
    (h1 : S ⊆ line w₁) (h2 : S ⊆ line w₂) (hc : 2 ≤ S.card) : w₁ = w₂ := by
  by_contra hne
  have hsub : S ⊆ line w₁ ∩ line w₂ := Finset.subset_inter h1 h2
  have hle := Finset.card_le_card hsub
  rw [card_inter_line w₁ w₂ hne] at hle
  omega

lemma line_eq_of_superset_le6 {S : Finset (Fin 13)} {w₁ w₂ : Fin 13}
    (h1 : line w₁ ⊆ S) (h2 : line w₂ ⊆ S) (hc : S.card ≤ 6) : w₁ = w₂ := by
  by_contra hne
  have hun : line w₁ ∪ line w₂ ⊆ S := Finset.union_subset h1 h2
  have hle := Finset.card_le_card hun
  have hci := Finset.card_union_add_card_inter (line w₁) (line w₂)
  rw [card_line w₁, card_line w₂, card_inter_line w₁ w₂ hne] at hci
  omega

lemma lines_in_card7_le2 (S : Finset (Fin 13)) (hc : S.card = 7) :
    (Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)).card ≤ 2 := by
  set T := Finset.univ.filter (fun w : Fin 13 => line w ⊆ S)
  by_contra hgt
  have h3 : 2 < T.card := by omega
  obtain ⟨w₁, hw₁, w₂, hw₂, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hrem : (T.erase w₁ |>.erase w₂).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hcard : (T.erase w₁ |>.erase w₂).card = 0 := by rw [hemp]; rfl
    have h1 : (T.erase w₁).card = T.card - 1 := Finset.card_erase_of_mem hw₁
    have hw2' : w₂ ∈ T.erase w₁ := Finset.mem_erase.mpr ⟨h12.symm, hw₂⟩
    have h2 : (T.erase w₁ |>.erase w₂).card = (T.erase w₁).card - 1 := Finset.card_erase_of_mem hw2'
    omega
  obtain ⟨w₃, hw₃⟩ := hrem
  have hw3_2 : w₃ ≠ w₂ := (Finset.mem_erase.mp hw₃).1
  have hw3_1 : w₃ ≠ w₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hw₃).2).1
  have hw3_T : w₃ ∈ T := (Finset.mem_erase.mp (Finset.mem_erase.mp hw₃).2).2
  have hL1 : line w₁ ⊆ S := (Finset.mem_filter.mp hw₁).2
  have hL2 : line w₂ ⊆ S := (Finset.mem_filter.mp hw₂).2
  have hL3 : line w₃ ⊆ S := (Finset.mem_filter.mp hw3_T).2
  have hun : (line w₁ ∪ line w₂) ∪ line w₃ ⊆ S :=
    Finset.union_subset (Finset.union_subset hL1 hL2) hL3
  have h12u : (line w₁ ∪ line w₂).card = 7 := by
    have hci := Finset.card_union_add_card_inter (line w₁) (line w₂)
    rw [card_line w₁, card_line w₂, card_inter_line w₁ w₂ h12] at hci
    omega
  have hinter : ((line w₁ ∪ line w₂) ∩ line w₃).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have hu := Finset.card_union_le (line w₁ ∩ line w₃) (line w₂ ∩ line w₃)
    rw [card_inter_line w₁ w₃ hw3_1.symm, card_inter_line w₂ w₃ hw3_2.symm] at hu
    omega
  have htot := Finset.card_union_add_card_inter (line w₁ ∪ line w₂) (line w₃)
  rw [h12u, card_line w₃] at htot
  have hle := Finset.card_le_card hun
  omega

-- Light inputs and monotonicity helpers
def e1 (v : Fin 13) : Fin 13 → Bool := fun k => decide (k = v)
def e2 (a b : Fin 13) : Fin 13 → Bool := fun k => decide (k = a ∨ k = b)

def WeightLe2 (x : Fin 13 → Bool) : Prop :=
  ∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k

lemma e1_weightLe2 (v : Fin 13) : WeightLe2 (e1 v) := by
  intro i j k hi hj hk
  simp only [e1, decide_eq_true_eq] at hi hj hk
  left; exact hi.trans hj.symm

lemma e2_weightLe2 (a b : Fin 13) : WeightLe2 (e2 a b) := by
  intro i j k hi hj hk
  simp only [e2, decide_eq_true_eq] at hi hj hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;> tauto

def MonoFun (f : (Fin 13 → Bool) → Bool) : Prop :=
  ∀ x y : Fin 13 → Bool, (∀ k, x k = true → y k = true) → f x = true → f y = true

def Safe (w : Fin 13) (f : (Fin 13 → Bool) → Bool) : Prop :=
  ∀ x : Fin 13 → Bool, WeightLe2 x → f x = true → ∃ v ∈ line w, x v = true

lemma prime_weight2 (w : Fin 13) (f₁ f₂ : (Fin 13 → Bool) → Bool)
    (hm₁ : MonoFun f₁) (hm₂ : MonoFun f₂)
    (hs : Safe w (fun x => f₁ x && f₂ x)) :
    (∀ v : Fin 13, f₁ (e1 v) = true → v ∈ line w) ∨
    (∀ v : Fin 13, f₂ (e1 v) = true → v ∈ line w) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨a, ha1, haL⟩, ⟨b, hb2, hbL⟩⟩ := h
  have h1 : f₁ (e2 a b) = true := hm₁ (e1 a) (e2 a b) (by
    intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk) ha1
  have h2 : f₂ (e2 a b) = true := hm₂ (e1 b) (e2 a b) (by
    intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk) hb2
  obtain ⟨v, hvL, hvx⟩ := hs (e2 a b) (e2_weightLe2 a b) (by simp [h1, h2])
  simp only [e2, decide_eq_true_eq] at hvx
  rcases hvx with rfl | rfl
  · exact haL hvL
  · exact hbL hvL

-- Wire evaluation and weight-1 support V
def wval (gates : List Gate) (i : ℕ) (x : Fin 13 → Bool) : Bool :=
  (wiresFrom gates (List.ofFn x)).getD i false

def wvalAt (gates : List Gate) (k i : ℕ) (x : Fin 13 → Bool) : Bool :=
  if i < 13 + k then wval gates i x else false

def V (gates : List Gate) (i : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun v => wval gates i (e1 v) = true)

def VAt (gates : List Gate) (k i : ℕ) : Finset (Fin 13) :=
  if i < 13 + k then V gates i else ∅

lemma mem_V (gates : List Gate) (i : ℕ) (v : Fin 13) :
    v ∈ V gates i ↔ wval gates i (e1 v) = true := by
  simp [V]

lemma mem_VAt (gates : List Gate) (k i : ℕ) (v : Fin 13) :
    v ∈ VAt gates k i ↔ wvalAt gates k i (e1 v) = true := by
  unfold VAt wvalAt
  split_ifs with h
  · exact mem_V gates i v
  · simp

lemma wval_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (i : ℕ) :
    MonoFun (wval gates i) := by
  intro x y hle hx
  apply wiresFrom_mono gates hmono (List.ofFn x) (List.ofFn y) (by simp) _ i hx
  intro j hj
  by_cases hjlt : j < 13
  · rw [List.getD_eq_getElem _ _ (by simpa using hjlt)] at hj ⊢
    simp only [List.getElem_ofFn] at hj ⊢
    exact hle ⟨j, hjlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

lemma wvalAt_mono (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (k i : ℕ) :
    MonoFun (wvalAt gates k i) := by
  intro x y hle hx
  unfold wvalAt at hx ⊢
  split_ifs at hx ⊢ with h
  exact wval_mono gates hmono i x y hle hx

lemma wval_input (gates : List Gate) (i : ℕ) (hi : i < 13) (x : Fin 13 → Bool) :
    wval gates i x = x ⟨i, hi⟩ := by
  unfold wval
  have hlen : (List.ofFn x).length = 13 := List.length_ofFn
  rw [getD_wiresFrom_lt gates (List.ofFn x) i (by omega)]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_ofFn (f := x) (i := i) (by omega)

lemma V_input (gates : List Gate) (i : ℕ) (hi : i < 13) :
    V gates i = {⟨i, hi⟩} := by
  ext v
  rw [mem_V, wval_input gates i hi, Finset.mem_singleton]
  simp [e1, Fin.ext_iff, eq_comm]

lemma card_V_input (gates : List Gate) (i : ℕ) (hi : i < 13) :
    (V gates i).card = 1 := by
  rw [V_input gates i hi, Finset.card_singleton]

lemma V_ge_len (gates : List Gate) (i : ℕ) (hi : 13 + gates.length ≤ i) :
    V gates i = ∅ := by
  ext v
  rw [mem_V]
  simp only [Finset.notMem_empty, iff_false]
  unfold wval
  rw [List.getD_eq_default]
  · simp
  · rw [length_wiresFrom, List.length_ofFn]; omega

lemma gate_idx_of_VAt_ge2 (gates : List Gate) (k i : ℕ) (hc : 2 ≤ (VAt gates k i).card) :
    ∃ g' < k, i = 13 + g' := by
  unfold VAt at hc
  split_ifs at hc with hlt
  · have hge13 : 13 ≤ i := by
      by_contra h13
      have hcard := card_V_input gates i (by omega)
      omega
    exact ⟨i - 13, by omega, by omega⟩
  · simp at hc

lemma gate_idx_of_V_ge2 (gates : List Gate) (i : ℕ) (hc : 2 ≤ (V gates i).card) :
    ∃ g < gates.length, i = 13 + g := by
  have hlt : i < 13 + gates.length := by
    by_contra hge
    have he := V_ge_len gates i (by omega)
    rw [he] at hc; simp at hc
  have hge13 : 13 ≤ i := by
    by_contra h13
    have hcard := card_V_input gates i (by omega)
    omega
  exact ⟨i - 13, by omega, by omega⟩

lemma wval_gate_eq (gates : List Gate) (k : ℕ) (hk : k < gates.length) (x : Fin 13 → Bool) :
    wval gates (13 + k) x =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i => wvalAt gates k i x) := by
  have h := getD_wiresFrom_gate gates (List.ofFn x) k hk
  rw [List.length_ofFn] at h
  exact h

lemma V_gate_nil_and (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = []) :
    V gates (13 + k) = Finset.univ := by
  ext v
  rw [mem_V, wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma V_gate_nil_or (gates : List Gate) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = []) :
    V gates (13 + k) = ∅ := by
  ext v
  rw [mem_V, wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma wval_gate_one (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a : ℕ)
    (hop : (gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or)
    (hin : (gates[k]).inputs = [a]) (x : Fin 13 → Bool) :
    wval gates (13 + k) x = wvalAt gates k a x := by
  rw [wval_gate_eq gates k hk, hin]
  rcases hop with h | h <;> simp [h, GateOp.eval]

lemma wval_gate_two_and (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = [a, b]) (x : Fin 13 → Bool) :
    wval gates (13 + k) x = (wvalAt gates k a x && wvalAt gates k b x) := by
  rw [wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma wval_gate_two_or (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = [a, b]) (x : Fin 13 → Bool) :
    wval gates (13 + k) x = (wvalAt gates k a x || wvalAt gates k b x) := by
  rw [wval_gate_eq gates k hk, hop, hin]
  simp [GateOp.eval]

lemma V_gate_one (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a : ℕ)
    (hop : (gates[k]).op = GateOp.and ∨ (gates[k]).op = GateOp.or)
    (hin : (gates[k]).inputs = [a]) :
    V gates (13 + k) = VAt gates k a := by
  ext v; rw [mem_V, mem_VAt, wval_gate_one gates k hk a hop hin]

lemma V_gate_two_and (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.and) (hin : (gates[k]).inputs = [a, b]) :
    V gates (13 + k) = VAt gates k a ∩ VAt gates k b := by
  ext v; rw [mem_V, Finset.mem_inter, mem_VAt, mem_VAt, wval_gate_two_and gates k hk a b hop hin]
  simp [Bool.and_eq_true]

lemma V_gate_two_or (gates : List Gate) (k : ℕ) (hk : k < gates.length) (a b : ℕ)
    (hop : (gates[k]).op = GateOp.or) (hin : (gates[k]).inputs = [a, b]) :
    V gates (13 + k) = VAt gates k a ∪ VAt gates k b := by
  ext v; rw [mem_V, Finset.mem_union, mem_VAt, mem_VAt, wval_gate_two_or gates k hk a b hop hin]
  simp [Bool.or_eq_true]

-- Owned gate sets and triple-superset predicate
def GwUp (gates : List Gate) (w : Fin 13) (g : ℕ) : Finset ℕ :=
  (Finset.range (g + 1)).filter (fun j => V gates (13 + j) ⊆ line w ∧ 2 ≤ (V gates (13 + j)).card)

def Gw (gates : List Gate) (w : Fin 13) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => V gates (13 + j) ⊆ line w ∧ 2 ≤ (V gates (13 + j)).card)

def HasTriple (gates : List Gate) (w : Fin 13) : Prop :=
  ∃ ga gb gc : ℕ,
    ga < gates.length ∧ gb < gates.length ∧ gc < gates.length ∧
    line w ⊂ V gates (13 + ga) ∧ line w ⊂ V gates (13 + gb) ∧ line w ⊂ V gates (13 + gc) ∧
    Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gb) \ line w) ∧
    Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gc) \ line w) ∧
    Disjoint (V gates (13 + gb) \ line w) (V gates (13 + gc) \ line w)

lemma GwUp_subset_Gw (gates : List Gate) (w : Fin 13) (g : ℕ) (hg : g < gates.length) :
    GwUp gates w g ⊆ Gw gates w := by
  intro j hj
  simp only [GwUp, Gw, Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by omega, hj.2⟩

lemma card_ge3_of_three {S : Finset ℕ} {a b c : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ S.card := by
  have hsub : ({a, b, c} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac])]
    rw [Finset.card_insert_of_notMem (by simp [hbc])]
    simp
  linarith [Finset.card_le_card hsub]

lemma card_ge2_of_two {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    2 ≤ S.card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({a, b} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hab])]; simp
  linarith [Finset.card_le_card hsub]

lemma card_ge3_of_sub (gates : List Gate) (w : Fin 13) (g' g : ℕ)
    (hlt : g' < g) (hg : g ∈ GwUp gates w g) (h2 : 2 ≤ (GwUp gates w g').card) :
    3 ≤ (GwUp gates w g).card := by
  have hnot : g ∉ GwUp gates w g' := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    omega
  have hsub : insert g (GwUp gates w g') ⊆ GwUp gates w g := by
    intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact hg
    · simp only [GwUp, Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, hj.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

-- Helper: any gate g' with V(13+g') ⊆ line w, card = 3, and Safe w has an earlier gate in GwUp
lemma exists_child_of_card3 (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (g' : ℕ) (hg' : g' < gates.length)
    (hsub : V gates (13 + g') ⊆ line w) (hcard : (V gates (13 + g')).card = 3)
    (hsafe : Safe w (wval gates (13 + g'))) :
    ∃ g'' < g', V gates (13 + g'') ⊆ line w ∧ 2 ≤ (V gates (13 + g'')).card := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
  obtain ⟨hop, hlen⟩ := hvalid (gates[g']) (List.getElem_mem hg')
  match hin : (gates[g']).inputs with
  | [] =>
    rcases hop with h | h
    · have hV := V_gate_nil_and gates g' hg' h hin
      rw [hV] at hcard; simp at hcard
    · have hV := V_gate_nil_or gates g' hg' h hin
      rw [hV] at hcard; simp at hcard
  | [a] =>
    have hV := V_gate_one gates g' hg' a hop hin
    have ha3 : (VAt gates g' a).card = 3 := by rw [← hV]; exact hcard
    obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by omega)
    have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
    rw [hVeq] at hV ha3
    exact ⟨g'', hg''lt, by rw [← hV]; exact hsub, by omega⟩
  | [a, b] =>
    rcases hop with h | h
    · have hw : ∀ x, wval gates (13 + g') x = (wvalAt gates g' a x && wvalAt gates g' b x) :=
        wval_gate_two_and gates g' hg' a b h hin
      have hsafe' : Safe w (fun x => wvalAt gates g' a x && wvalAt gates g' b x) := by
        intro x hx hv; exact hsafe x hx (by rw [hw]; exact hv)
      have hV := V_gate_two_and gates g' hg' a b h hin
      have hpr := prime_weight2 w (wvalAt gates g' a) (wvalAt gates g' b)
        (wvalAt_mono gates hmono g' a) (wvalAt_mono gates hmono g' b) hsafe'
      rcases hpr with haL | hbL
      · have hasub : VAt gates g' a ⊆ line w := by
          intro v hv; exact haL v ((mem_VAt gates g' a v).mp hv)
        have hge : 3 ≤ (VAt gates g' a).card := by
          have := Finset.card_le_card (Finset.inter_subset_left (s₁ := VAt gates g' a) (s₂ := VAt gates g' b))
          rw [← hV, hcard] at this; exact this
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by omega)
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        rw [hVeq] at hasub hge
        exact ⟨g'', hg''lt, hasub, by omega⟩
      · have hbsub : VAt gates g' b ⊆ line w := by
          intro v hv; exact hbL v ((mem_VAt gates g' b v).mp hv)
        have hge : 3 ≤ (VAt gates g' b).card := by
          have := Finset.card_le_card (Finset.inter_subset_right (s₁ := VAt gates g' a) (s₂ := VAt gates g' b))
          rw [← hV, hcard] at this; exact this
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b (by omega)
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        rw [hVeq] at hbsub hge
        exact ⟨g'', hg''lt, hbsub, by omega⟩
    · have hV := V_gate_two_or gates g' hg' a b h hin
      have hsum : 3 ≤ (VAt gates g' a).card + (VAt gates g' b).card := by
        have := Finset.card_union_le (VAt gates g' a) (VAt gates g' b)
        rw [← hV, hcard] at this; exact this
      by_cases ha2 : 2 ≤ (VAt gates g' a).card
      · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a ha2
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        have hasub : V gates (13 + g'') ⊆ line w := by
          rw [← hVeq]; exact Finset.subset_union_left.trans (by rw [← hV]; exact hsub)
        exact ⟨g'', hg''lt, hasub, by rw [← hVeq]; exact ha2⟩
      · have hb2 : 2 ≤ (VAt gates g' b).card := by omega
        obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b hb2
        have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
        have hbsub : V gates (13 + g'') ⊆ line w := by
          rw [← hVeq]; exact Finset.subset_union_right.trans (by rw [← hV]; exact hsub)
        exact ⟨g'', hg''lt, hbsub, by rw [← hVeq]; exact hb2⟩
  | _ :: _ :: _ :: _ =>
    rw [hin] at hlen; simp at hlen

-- Helper: symmetric core of the AND case when VAt g i = line w and line w ⊆ VAt g j
lemma and_case_core (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (g : ℕ) (hg : g < gates.length)
    (hVg : V gates (13 + g) = line w)
    (hsafe : Safe w (wval gates (13 + g)))
    (ih : ∀ m < g, V gates (13 + m) = line w → Safe w (wval gates (13 + m)) →
      3 ≤ (GwUp gates w m).card ∨ (2 ≤ (GwUp gates w m).card ∧ HasTriple gates w))
    (i j : ℕ) (hwg : ∀ x, wval gates (13 + g) x = (wvalAt gates g i x && wvalAt gates g j x))
    (hVi : VAt gates g i = line w) (hVj_sub : line w ⊆ VAt gates g j) :
    3 ≤ (GwUp gates w g).card ∨ (2 ≤ (GwUp gates w g).card ∧ HasTriple gates w) := by
  have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
  have hgw : g ∈ GwUp gates w g := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_self g, by rw [hVg], by rw [hVg, card_line]; omega⟩
  have hi2 : 2 ≤ (VAt gates g i).card := by rw [hVi, card_line]; omega
  obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i hi2
  have hVi_eq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
  rw [hVi_eq] at hVi
  have hg'w : g' ∈ GwUp gates w g := by
    simp only [GwUp, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [hVi], by rw [hVi, card_line]; omega⟩
  -- Case 1: VAt g j = line w
  by_cases hVj_eq : VAt gates g j = line w
  · by_cases hji : j = 13 + g'
    · subst hji
      have hsafe' : Safe w (wval gates (13 + g')) := by
        intro x hx hv
        have h1 : wvalAt gates g (13 + g') x = true := by
          unfold wvalAt; rw [if_pos (by omega)]; exact hv
        exact hsafe x hx (by rw [hwg]; simp [h1])
      have hih := ih g' hg'lt hVi hsafe'
      have h2' : 2 ≤ (GwUp gates w g').card := by
        rcases hih with h3 | ⟨h2, _⟩ <;> omega
      exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
    · have hj2 : 2 ≤ (VAt gates g j).card := by rw [hVj_eq, card_line]; omega
      obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j hj2
      have hVj_eq2 : VAt gates g (13 + g'') = V gates (13 + g'') := if_pos (by omega)
      rw [hVj_eq2] at hVj_eq
      have hg''w : g'' ∈ GwUp gates w g := by
        simp only [GwUp, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hVj_eq], by rw [hVj_eq, card_line]; omega⟩
      exact Or.inl (card_ge3_of_three hg'w hg''w hgw (by omega) (by omega) (by omega))
  -- Case 2: line w ⊂ VAt g j
  · have hVj_ssub : line w ⊂ VAt gates g j := Finset.ssubset_iff_subset_ne.mpr ⟨hVj_sub, fun he => hVj_eq he.symm⟩
    have hj5 : 5 ≤ (VAt gates g j).card := by
      have := Finset.card_lt_card hVj_ssub
      rw [card_line] at this; omega
    obtain ⟨gj, hgjlt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
    have hVj_eq2 : VAt gates g (13 + gj) = V gates (13 + gj) := if_pos (by omega)
    rw [hVj_eq2] at hVj_ssub
    -- Now inspect gate g' (which has V gates (13 + g') = line w)
    have hg'_len : g' < gates.length := by omega
    obtain ⟨hop', hlen'⟩ := hvalid (gates[g']) (List.getElem_mem hg'_len)
    match hin' : (gates[g']).inputs with
    | [] =>
      rcases hop' with h | h
      · have hV := V_gate_nil_and gates g' hg'_len h hin'
        rw [hV] at hVi
        have := congrArg Finset.card hVi
        rw [card_line] at this; simp at this
      · have hV := V_gate_nil_or gates g' hg'_len h hin'
        rw [hV] at hVi
        have := congrArg Finset.card hVi
        rw [card_line] at this; simp at this
    | [a] =>
      have hV := V_gate_one gates g' hg'_len a hop' hin'
      rw [hVi] at hV
      obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by rw [← hV, card_line]; omega)
      have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
      rw [hVeq] at hV
      have hg''w : g'' ∈ GwUp gates w g := by
        simp only [GwUp, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [← hV], by rw [← hV, card_line]; omega⟩
      exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
    | [a, b] =>
      rcases hop' with h | h
      · have hV := V_gate_two_and gates g' hg'_len a b h hin'
        rw [hVi] at hV
        have ha_sub : line w ⊆ VAt gates g' a := by
          rw [hV]; exact Finset.inter_subset_left
        have hb_sub : line w ⊆ VAt gates g' b := by
          rw [hV]; exact Finset.inter_subset_right
        by_cases ha_eq : VAt gates g' a = line w
        · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by rw [ha_eq, card_line]; omega)
          have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
          rw [hVeq] at ha_eq
          have hg''w : g'' ∈ GwUp gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, by rw [ha_eq], by rw [ha_eq, card_line]; omega⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
        · by_cases hb_eq : VAt gates g' b = line w
          · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b (by rw [hb_eq, card_line]; omega)
            have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
            rw [hVeq] at hb_eq
            have hg''w : g'' ∈ GwUp gates w g := by
              simp only [GwUp, Finset.mem_filter, Finset.mem_range]
              exact ⟨by omega, by rw [hb_eq], by rw [hb_eq, card_line]; omega⟩
            exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
          · -- Strict supersets: ga, gb, gj!
            have ha_ssub : line w ⊂ VAt gates g' a := Finset.ssubset_iff_subset_ne.mpr ⟨ha_sub, fun he => ha_eq he.symm⟩
            have hb_ssub : line w ⊂ VAt gates g' b := Finset.ssubset_iff_subset_ne.mpr ⟨hb_sub, fun he => hb_eq he.symm⟩
            have ha5 : 5 ≤ (VAt gates g' a).card := by
              have := Finset.card_lt_card ha_ssub; rw [card_line] at this; omega
            have hb5 : 5 ≤ (VAt gates g' b).card := by
              have := Finset.card_lt_card hb_ssub; rw [card_line] at this; omega
            obtain ⟨ga, hgalt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a (by omega)
            obtain ⟨gb, hgblt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b (by omega)
            have hVa_eq : VAt gates g' (13 + ga) = V gates (13 + ga) := if_pos (by omega)
            have hVb_eq : VAt gates g' (13 + gb) = V gates (13 + gb) := if_pos (by omega)
            rw [hVa_eq] at ha_ssub
            rw [hVb_eq] at hb_ssub
            rw [hVa_eq, hVb_eq] at hV
            have hdisj_ab : Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gb) \ line w) := by
              rw [Finset.disjoint_left]
              intro p hpa hpb
              rw [Finset.mem_sdiff] at hpa hpb
              have hp_in : p ∈ V gates (13 + ga) ∩ V gates (13 + gb) := Finset.mem_inter.mpr ⟨hpa.1, hpb.1⟩
              rw [← hV] at hp_in
              exact hpa.2 hp_in
            have hwg' : ∀ x, wval gates (13 + g') x = (wval gates (13 + ga) x && wval gates (13 + gb) x) := by
              intro x
              rw [wval_gate_two_and gates g' hg'_len (13 + ga) (13 + gb) h hin']
              unfold wvalAt
              rw [if_pos (by omega), if_pos (by omega)]
            have hdisj_aj : Disjoint (V gates (13 + ga) \ line w) (V gates (13 + gj) \ line w) := by
              rw [Finset.disjoint_left]
              intro p hpa hpj
              rw [Finset.mem_sdiff] at hpa hpj
              obtain ⟨q, hqb, hqL⟩ := Finset.exists_of_ssubset hb_ssub
              have h1 : wval gates (13 + ga) (e2 p q) = true :=
                wval_mono gates hmono (13 + ga) (e1 p) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V gates (13 + ga) p).mp hpa.1)
              have h2 : wval gates (13 + gb) (e2 p q) = true :=
                wval_mono gates hmono (13 + gb) (e1 q) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V gates (13 + gb) q).mp hqb)
              have h3 : wval gates (13 + gj) (e2 p q) = true :=
                wval_mono gates hmono (13 + gj) (e1 p) (e2 p q)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V gates (13 + gj) p).mp hpj.1)
              have hval : wval gates (13 + g) (e2 p q) = true := by
                rw [hwg]
                unfold wvalAt
                rw [if_pos (by omega), if_pos (by omega), hwg']
                simp [h1, h2, h3]
              obtain ⟨v, hvL, hvx⟩ := hsafe (e2 p q) (e2_weightLe2 p q) hval
              simp only [e2, decide_eq_true_eq] at hvx
              rcases hvx with rfl | rfl
              · exact hpa.2 hvL
              · exact hqL hvL
            have hdisj_bj : Disjoint (V gates (13 + gb) \ line w) (V gates (13 + gj) \ line w) := by
              rw [Finset.disjoint_left]
              intro p hpb hpj
              rw [Finset.mem_sdiff] at hpb hpj
              obtain ⟨q, hqa, hqL⟩ := Finset.exists_of_ssubset ha_ssub
              have h1 : wval gates (13 + ga) (e2 q p) = true :=
                wval_mono gates hmono (13 + ga) (e1 q) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inl hk)
                  ((mem_V gates (13 + ga) q).mp hqa)
              have h2 : wval gates (13 + gb) (e2 q p) = true :=
                wval_mono gates hmono (13 + gb) (e1 p) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V gates (13 + gb) p).mp hpb.1)
              have h3 : wval gates (13 + gj) (e2 q p) = true :=
                wval_mono gates hmono (13 + gj) (e1 p) (e2 q p)
                  (by intro k hk; simp only [e1, e2, decide_eq_true_eq] at hk ⊢; exact Or.inr hk)
                  ((mem_V gates (13 + gj) p).mp hpj.1)
              have hval : wval gates (13 + g) (e2 q p) = true := by
                rw [hwg]
                unfold wvalAt
                rw [if_pos (by omega), if_pos (by omega), hwg']
                simp [h1, h2, h3]
              obtain ⟨v, hvL, hvx⟩ := hsafe (e2 q p) (e2_weightLe2 q p) hval
              simp only [e2, decide_eq_true_eq] at hvx
              rcases hvx with rfl | rfl
              · exact hqL hvL
              · exact hpb.2 hvL
            exact Or.inr ⟨card_ge2_of_two hg'w hgw (by omega),
              ⟨ga, gb, gj, by omega, by omega, by omega,
                ha_ssub, hb_ssub, hVj_ssub, hdisj_ab, hdisj_aj, hdisj_bj⟩⟩
      · have hV := V_gate_two_or gates g' hg'_len a b h hin'
        rw [hVi] at hV
        have hsum : 4 ≤ (VAt gates g' a).card + (VAt gates g' b).card := by
          have := Finset.card_union_le (VAt gates g' a) (VAt gates g' b)
          rw [← hV, card_line] at this; exact this
        by_cases ha2 : 2 ≤ (VAt gates g' a).card
        · obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' a ha2
          have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
          have hasub : V gates (13 + g'') ⊆ line w := by
            rw [← hVeq, hV]; exact Finset.subset_union_left
          have hg''w : g'' ∈ GwUp gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hasub, by rw [← hVeq]; exact ha2⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
        · have hb2 : 2 ≤ (VAt gates g' b).card := by omega
          obtain ⟨g'', hg''lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g' b hb2
          have hVeq : VAt gates g' (13 + g'') = V gates (13 + g'') := if_pos (by omega)
          have hbsub : V gates (13 + g'') ⊆ line w := by
            rw [← hVeq, hV]; exact Finset.subset_union_right
          have hg''w : g'' ∈ GwUp gates w g := by
            simp only [GwUp, Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hbsub, by rw [← hVeq]; exact hb2⟩
          exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
    | _ :: _ :: _ :: _ =>
      rw [hin'] at hlen'; simp at hlen'

-- Main per-line structural lemma by strong induction on gate index g
lemma line_structure (gates : List Gate)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) :
    ∀ g : ℕ, g < gates.length → V gates (13 + g) = line w → Safe w (wval gates (13 + g)) →
      3 ≤ (GwUp gates w g).card ∨ (2 ≤ (GwUp gates w g).card ∧ HasTriple gates w) := by
  intro g
  induction g using Nat.strongRecOn with
  | ind g ih =>
    intro hg hVg hsafe
    have hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hvalid g hg).1
    have hgw : g ∈ GwUp gates w g := by
      simp only [GwUp, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_self g, by rw [hVg], by rw [hVg, card_line]; omega⟩
    obtain ⟨hop, hlen⟩ := hvalid (gates[g]) (List.getElem_mem hg)
    match hin : (gates[g]).inputs with
    | [] =>
      rcases hop with h | h
      · have hV := V_gate_nil_and gates g hg h hin
        rw [hV] at hVg
        have := congrArg Finset.card hVg; rw [card_line] at this; simp at this
      · have hV := V_gate_nil_or gates g hg h hin
        rw [hV] at hVg
        have := congrArg Finset.card hVg; rw [card_line] at this; simp at this
    | [a] =>
      have hV := V_gate_one gates g hg a hop hin
      rw [hVg] at hV
      obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g a (by rw [← hV, card_line]; omega)
      have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
      rw [hVeq] at hV
      have hsafe' : Safe w (wval gates (13 + g')) := by
        intro x hx hv
        apply hsafe x hx
        rw [wval_gate_one gates g hg (13 + g') hop hin]
        unfold wvalAt; rw [if_pos (by omega)]; exact hv
      have hih := ih g' hg'lt (by omega) hV.symm hsafe'
      have h2' : 2 ≤ (GwUp gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
      exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
    | [i, j] =>
      rcases hop with h | h
      · -- AND gate
        have hwg := wval_gate_two_and gates g hg i j h hin
        have hsafe' : Safe w (fun x => wvalAt gates g i x && wvalAt gates g j x) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; exact hv)
        have hV := V_gate_two_and gates g hg i j h hin
        rw [hVg] at hV
        have hpr := prime_weight2 w (wvalAt gates g i) (wvalAt gates g j)
          (wvalAt_mono gates hmono g i) (wvalAt_mono gates hmono g j) hsafe'
        have ih' : ∀ m < g, V gates (13 + m) = line w → Safe w (wval gates (13 + m)) →
            3 ≤ (GwUp gates w m).card ∨ (2 ≤ (GwUp gates w m).card ∧ HasTriple gates w) :=
          fun m hm => ih m hm (by omega)
        rcases hpr with hiL | hjL
        · have hisub : VAt gates g i ⊆ line w := fun v hv => hiL v ((mem_VAt gates g i v).mp hv)
          have hVi : VAt gates g i = line w :=
            Finset.Subset.antisymm hisub (by rw [hV]; exact Finset.inter_subset_left)
          have hVj_sub : line w ⊆ VAt gates g j := by rw [hV]; exact Finset.inter_subset_right
          exact and_case_core gates hvalid w g hg hVg hsafe ih' i j hwg hVi hVj_sub
        · have hjsub : VAt gates g j ⊆ line w := fun v hv => hjL v ((mem_VAt gates g j v).mp hv)
          have hVj : VAt gates g j = line w :=
            Finset.Subset.antisymm hjsub (by rw [hV]; exact Finset.inter_subset_right)
          have hVi_sub : line w ⊆ VAt gates g i := by rw [hV]; exact Finset.inter_subset_left
          have hwg_comm : ∀ x, wval gates (13 + g) x = (wvalAt gates g j x && wvalAt gates g i x) := by
            intro x; rw [hwg, Bool.and_comm]
          exact and_case_core gates hvalid w g hg hVg hsafe ih' j i hwg_comm hVj hVi_sub
      · -- OR gate
        have hwg := wval_gate_two_or gates g hg i j h hin
        have hV := V_gate_two_or gates g hg i j h hin
        rw [hVg] at hV
        have hi_sub : VAt gates g i ⊆ line w := by rw [hV]; exact Finset.subset_union_left
        have hj_sub : VAt gates g j ⊆ line w := by rw [hV]; exact Finset.subset_union_right
        have hsafe_i : Safe w (wvalAt gates g i) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; simp [hv])
        have hsafe_j : Safe w (wvalAt gates g j) := by
          intro x hx hv; exact hsafe x hx (by rw [hwg]; simp [hv])
        have hci_le : (VAt gates g i).card ≤ 4 := by
          have := Finset.card_le_card hi_sub; rw [card_line] at this; exact this
        have hcj_le : (VAt gates g j).card ≤ 4 := by
          have := Finset.card_le_card hj_sub; rw [card_line] at this; exact this
        have hsum : 4 ≤ (VAt gates g i).card + (VAt gates g j).card := by
          have := Finset.card_union_le (VAt gates g i) (VAt gates g j)
          rw [← hV, card_line] at this; exact this
        by_cases hi4 : (VAt gates g i).card = 4
        · have hVi : VAt gates g i = line w :=
            Finset.eq_of_subset_of_card_le hi_sub (by rw [card_line, hi4])
          obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i (by omega)
          have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
          rw [hVeq] at hVi
          have hsafe' : Safe w (wval gates (13 + g')) := by
            intro x hx hv; exact hsafe_i x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
          have hih := ih g' hg'lt (by omega) hVi hsafe'
          have h2' : 2 ≤ (GwUp gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
          exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
        · by_cases hj4 : (VAt gates g j).card = 4
          · have hVj : VAt gates g j = line w :=
              Finset.eq_of_subset_of_card_le hj_sub (by rw [card_line, hj4])
            obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
            have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
            rw [hVeq] at hVj
            have hsafe' : Safe w (wval gates (13 + g')) := by
              intro x hx hv; exact hsafe_j x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
            have hih := ih g' hg'lt (by omega) hVj hsafe'
            have h2' : 2 ≤ (GwUp gates w g').card := by rcases hih with h3 | ⟨h2, _⟩ <;> omega
            exact Or.inl (card_ge3_of_sub gates w g' g hg'lt hgw h2')
          · by_cases hi3 : (VAt gates g i).card = 3
            · obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i (by omega)
              have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
              rw [hVeq] at hi_sub hi3
              have hsafe' : Safe w (wval gates (13 + g')) := by
                intro x hx hv; exact hsafe_i x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
              obtain ⟨g'', hg''lt, hsub'', hc''⟩ :=
                exists_child_of_card3 gates hvalid w g' (by omega) hi_sub hi3 hsafe'
              have hg'w : g' ∈ GwUp gates w g := by
                simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, hi_sub, by omega⟩
              have hg''w : g'' ∈ GwUp gates w g := by
                simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                exact ⟨by omega, hsub'', hc''⟩
              exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
            · by_cases hj3 : (VAt gates g j).card = 3
              · obtain ⟨g', hg'lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
                have hVeq : VAt gates g (13 + g') = V gates (13 + g') := if_pos (by omega)
                rw [hVeq] at hj_sub hj3
                have hsafe' : Safe w (wval gates (13 + g')) := by
                  intro x hx hv; exact hsafe_j x hx (by unfold wvalAt; rw [if_pos (by omega)]; exact hv)
                obtain ⟨g'', hg''lt, hsub'', hc''⟩ :=
                  exists_child_of_card3 gates hvalid w g' (by omega) hj_sub hj3 hsafe'
                have hg'w : g' ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hj_sub, by omega⟩
                have hg''w : g'' ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hsub'', hc''⟩
                exact Or.inl (card_ge3_of_three hg''w hg'w hgw (by omega) (by omega) (by omega))
              · -- Both have card = 2!
                have hi2 : (VAt gates g i).card = 2 := by omega
                have hj2 : (VAt gates g j).card = 2 := by omega
                have hij_ne : i ≠ j := by
                  intro he; subst he
                  rw [Finset.union_idempotent] at hV
                  have := congrArg Finset.card hV
                  rw [card_line, hi2] at this; omega
                obtain ⟨g₁, hg₁lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g i (by omega)
                obtain ⟨g₂, hg₂lt, rfl⟩ := gate_idx_of_VAt_ge2 gates g j (by omega)
                have hV1 : VAt gates g (13 + g₁) = V gates (13 + g₁) := if_pos (by omega)
                have hV2 : VAt gates g (13 + g₂) = V gates (13 + g₂) := if_pos (by omega)
                rw [hV1] at hi_sub hi2
                rw [hV2] at hj_sub hj2
                have hg1w : g₁ ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hi_sub, by omega⟩
                have hg2w : g₂ ∈ GwUp gates w g := by
                  simp only [GwUp, Finset.mem_filter, Finset.mem_range]
                  exact ⟨by omega, hj_sub, by omega⟩
                exact Or.inl (card_ge3_of_three hg1w hg2w hgw (by omega) (by omega) (by omega))
    | _ :: _ :: _ :: _ =>
      rw [hin] at hlen; simp at hlen

-- From HasTriple, either some gate has card in {5, 6}, or all three have card = 7 and are distinct!
def B56 (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => 5 ≤ (V gates (13 + j)).card ∧ (V gates (13 + j)).card ≤ 6)

def B7 (gates : List Gate) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => (V gates (13 + j)).card = 7)

lemma card_sdiff_eq {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

lemma triple_split (gates : List Gate) (w : Fin 13) (ht : HasTriple gates w) :
    (∃ j ∈ B56 gates, line w ⊆ V gates (13 + j)) ∨
    3 ≤ ((B7 gates).filter (fun j => line w ⊆ V gates (13 + j))).card := by
  obtain ⟨ga, gb, gc, ha_lt, hb_lt, hc_lt, ha_ss, hb_ss, hc_ss, hab, hac, hbc⟩ := ht
  set Da := V gates (13 + ga) \ line w
  set Db := V gates (13 + gb) \ line w
  set Dc := V gates (13 + gc) \ line w
  have ha_sub : line w ⊆ V gates (13 + ga) := ha_ss.subset
  have hb_sub : line w ⊆ V gates (13 + gb) := hb_ss.subset
  have hc_sub : line w ⊆ V gates (13 + gc) := hc_ss.subset
  have hra_pos : 1 ≤ Da.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset ha_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hrb_pos : 1 ≤ Db.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset hb_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hrc_pos : 1 ≤ Dc.card := by
    obtain ⟨p, hp, hpn⟩ := Finset.exists_of_ssubset hc_ss
    exact Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpn⟩⟩
  have hca : (V gates (13 + ga)).card = 4 + Da.card := by
    have hle := Finset.card_le_card ha_sub
    have hsd : Da.card = (V gates (13 + ga)).card - (line w).card := card_sdiff_eq ha_sub
    rw [card_line] at hsd hle; omega
  have hcb : (V gates (13 + gb)).card = 4 + Db.card := by
    have hle := Finset.card_le_card hb_sub
    have hsd : Db.card = (V gates (13 + gb)).card - (line w).card := card_sdiff_eq hb_sub
    rw [card_line] at hsd hle; omega
  have hcc : (V gates (13 + gc)).card = 4 + Dc.card := by
    have hle := Finset.card_le_card hc_sub
    have hsd : Dc.card = (V gates (13 + gc)).card - (line w).card := card_sdiff_eq hc_sub
    rw [card_line] at hsd hle; omega
  have hsum : Da.card + Db.card + Dc.card ≤ 9 := by
    have hsub : (Da ∪ Db) ∪ Dc ⊆ Finset.univ \ line w := by
      intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with (hx | hx) | hx
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
    have hd_ab_c : Disjoint (Da ∪ Db) Dc := Finset.disjoint_union_left.mpr ⟨hac, hbc⟩
    have hc_u : ((Da ∪ Db) ∪ Dc).card = Da.card + Db.card + Dc.card := by
      rw [Finset.card_union_of_disjoint hd_ab_c, Finset.card_union_of_disjoint hab]
    have hc_comp : (Finset.univ \ line w).card = 9 := by
      rw [card_sdiff_eq (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, card_line]
    have := Finset.card_le_card hsub
    omega
  by_cases ha2 : Da.card ≤ 2
  · left
    exact ⟨ga, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, by omega, by omega⟩, ha_sub⟩
  · by_cases hb2 : Db.card ≤ 2
    · left
      exact ⟨gb, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, by omega, by omega⟩, hb_sub⟩
    · by_cases hc2 : Dc.card ≤ 2
      · left
        exact ⟨gc, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc_lt, by omega, by omega⟩, hc_sub⟩
      · right
        have ha7 : (V gates (13 + ga)).card = 7 := by omega
        have hb7 : (V gates (13 + gb)).card = 7 := by omega
        have hc7 : (V gates (13 + gc)).card = 7 := by omega
        have hne_ab : ga ≠ gb := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hra_pos
          exact Finset.disjoint_left.mp hab hp (by simpa [Da, Db, he] using hp)
        have hne_ac : ga ≠ gc := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hra_pos
          exact Finset.disjoint_left.mp hac hp (by simpa [Da, Dc, he] using hp)
        have hne_bc : gb ≠ gc := by
          intro he
          obtain ⟨p, hp⟩ := Finset.card_pos.mp hrb_pos
          exact Finset.disjoint_left.mp hbc hp (by simpa [Db, Dc, he] using hp)
        have hma : ga ∈ (B7 gates).filter (fun j => line w ⊆ V gates (13 + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha_lt, ha7⟩, ha_sub⟩
        have hmb : gb ∈ (B7 gates).filter (fun j => line w ⊆ V gates (13 + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb_lt, hb7⟩, hb_sub⟩
        have hmc : gc ∈ (B7 gates).filter (fun j => line w ⊆ V gates (13 + j)) :=
          Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc_lt, hc7⟩, hc_sub⟩
        exact card_ge3_of_three hma hmb hmc hne_ab hne_ac hne_bc

theorem main_lb (gates : List Gate) (out : Fin 13 → ℕ)
    (hvalid : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcomp : ∀ (w : Fin 13) (x : Fin 13 → Bool), WeightLe2 x →
      Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ line w, x v = true)) :
    39 ≤ gates.length := by
  -- Step 1: Every line w satisfies either 3 ≤ (Gw w).card or (2 ≤ (Gw w).card ∧ HasTriple w)
  have hline : ∀ w : Fin 13,
      3 ≤ (Gw gates w).card ∨ (2 ≤ (Gw gates w).card ∧ HasTriple gates w) := by
    intro w
    have hVout : V gates (out w) = line w := by
      ext v
      rw [mem_V]
      have hc := hcomp w (e1 v) (e1_weightLe2 v)
      change wval gates (out w) (e1 v) = decide (∃ u ∈ line w, e1 v u = true) at hc
      rw [hc, decide_eq_true_eq]
      constructor
      · rintro ⟨u, huL, hu⟩
        simp only [e1, decide_eq_true_eq] at hu
        rwa [← hu]
      · intro hvL
        exact ⟨v, hvL, by simp [e1]⟩
    have hsafe_out : Safe w (wval gates (out w)) := by
      intro x hx hv
      have hc := hcomp w x hx
      change wval gates (out w) x = decide (∃ u ∈ line w, x u = true) at hc
      rw [hc, decide_eq_true_eq] at hv
      exact hv
    obtain ⟨g, hglt, hgo⟩ := gate_idx_of_V_ge2 gates (out w) (by rw [hVout, card_line]; omega)
    rw [hgo] at hVout hsafe_out
    have hsub := Finset.card_le_card (GwUp_subset_Gw gates w g hglt)
    rcases line_structure gates hvalid w g hglt hVout hsafe_out with h3 | ⟨h2, ht⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, ht⟩
  -- Step 2: Gw w (across all w), B56, B7 are pairwise disjoint subsets of range gates.length
  have hGw_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 13)) (Gw gates) := by
    intro w₁ _ w₂ _ hne
    change Disjoint (Gw gates w₁) (Gw gates w₂)
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Gw, Finset.mem_filter] at hj₁ hj₂
    exact hne (line_eq_of_subset_two hj₁.2.1 hj₂.2.1 hj₁.2.2)
  set U := Finset.univ.biUnion (Gw gates)
  have hU_card : U.card = ∑ w : Fin 13, (Gw gates w).card :=
    Finset.card_biUnion (fun w₁ _ w₂ _ hne => hGw_disj (Finset.mem_univ w₁) (Finset.mem_univ w₂) hne)
  have hU_disj_56 : Disjoint U (B56 gates) := by
    rw [Finset.disjoint_left]
    intro j hjU hj56
    obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hjU
    simp only [Gw, B56, Finset.mem_filter] at hjw hj56
    have hle := Finset.card_le_card hjw.2.1
    rw [card_line] at hle
    omega
  have hU_disj_7 : Disjoint U (B7 gates) := by
    rw [Finset.disjoint_left]
    intro j hjU hj7
    obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hjU
    simp only [Gw, B7, Finset.mem_filter] at hjw hj7
    have hle := Finset.card_le_card hjw.2.1
    rw [card_line] at hle
    omega
  have h56_disj_7 : Disjoint (B56 gates) (B7 gates) := by
    rw [Finset.disjoint_left]
    intro j hj56 hj7
    simp only [B56, B7, Finset.mem_filter] at hj56 hj7
    omega
  have htot_sub : (U ∪ B56 gates) ∪ B7 gates ⊆ Finset.range gates.length := by
    intro j hj
    simp only [Finset.mem_union] at hj
    rcases hj with (hjU | hj56) | hj7
    · obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hjU
      exact (Finset.mem_filter.mp hjw).1
    · exact (Finset.mem_filter.mp hj56).1
    · exact (Finset.mem_filter.mp hj7).1
  have htot_le : (∑ w : Fin 13, (Gw gates w).card) + (B56 gates).card + (B7 gates).card ≤ gates.length := by
    have hc := Finset.card_le_card htot_sub
    rw [Finset.card_range] at hc
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hU_disj_7, h56_disj_7⟩),
        Finset.card_union_of_disjoint hU_disj_56, hU_card] at hc
    exact hc
  -- Step 3: Partition Fin 13 into W3, W56, W7
  set W3 := Finset.univ.filter (fun w : Fin 13 => 3 ≤ (Gw gates w).card)
  set Wrem := Finset.univ \ W3
  set W56 := Wrem.filter (fun w : Fin 13 => ∃ j ∈ B56 gates, line w ⊆ V gates (13 + j))
  set W7 := Wrem \ W56
  have hW56_sub : W56 ⊆ Wrem := Finset.filter_subset _ Wrem
  have h1_part : W56.card + W7.card = Wrem.card := by
    have hsd : W7.card = Wrem.card - W56.card := card_sdiff_eq hW56_sub
    have hle : W56.card ≤ Wrem.card := Finset.card_le_card hW56_sub
    omega
  have hpart : W3.card + W56.card + W7.card = 13 := by
    have hsd : Wrem.card = (Finset.univ : Finset (Fin 13)).card - W3.card := card_sdiff_eq (Finset.subset_univ W3)
    have hle : W3.card ≤ (Finset.univ : Finset (Fin 13)).card := Finset.card_le_card (Finset.subset_univ W3)
    rw [Finset.card_univ, Fintype.card_fin] at hsd hle
    omega
  -- Sum of |Gw w| >= 26 + W3.card = 3 * W3.card + 2 * W56.card + 2 * W7.card
  have hGw_sum : 3 * W3.card + 2 * W56.card + 2 * W7.card ≤ ∑ w : Fin 13, (Gw gates w).card := by
    have hge : ∀ w : Fin 13, (if w ∈ W3 then 3 else 2) ≤ (Gw gates w).card := by
      intro w
      split_ifs with hw
      · exact (Finset.mem_filter.mp hw).2
      · rcases hline w with h3 | ⟨h2, _⟩
        · omega
        · exact h2
    have hsum_le := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hge w)
    have hlhs : ∑ w : Fin 13, (if w ∈ W3 then (3 : ℕ) else 2) = 3 * W3.card + 2 * Wrem.card := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
      have hf1 : (Finset.univ.filter (fun w : Fin 13 => w ∈ W3)) = W3 := by
        ext x; simp
      have hf2 : (Finset.univ.filter (fun w : Fin 13 => w ∉ W3)) = Wrem := by
        ext x; simp [Wrem]
      rw [hf1, hf2]; ring
    omega
  -- Step 4: W56.card <= (B56 gates).card via injection
  have hW56_le : W56.card ≤ (B56 gates).card := by
    have hex : ∀ w ∈ W56, ∃ j ∈ B56 gates, line w ⊆ V gates (13 + j) :=
      fun w hw => (Finset.mem_filter.mp hw).2
    choose f hf_mem hf_sub using hex
    have hinj : Set.InjOn (fun w => if hw : w ∈ W56 then f w hw else 0) W56 := by
      intro w₁ hw₁ w₂ hw₂ heq
      have hw₁' : w₁ ∈ W56 := Finset.mem_coe.mp hw₁
      have hw₂' : w₂ ∈ W56 := Finset.mem_coe.mp hw₂
      have hf_eq : f w₁ hw₁' = f w₂ hw₂' := by simpa [hw₁', hw₂'] using heq
      have h1 := hf_sub w₁ hw₁'
      have h2 := hf_sub w₂ hw₂'
      rw [← hf_eq] at h2
      have hc6 : (V gates (13 + f w₁ hw₁')).card ≤ 6 := (Finset.mem_filter.mp (hf_mem w₁ hw₁')).2.2
      exact line_eq_of_superset_le6 h1 h2 hc6
    have hmap : ∀ w ∈ W56, (if hw : w ∈ W56 then f w hw else 0) ∈ B56 gates := by
      intro w hw; simp [hw, hf_mem w hw]
    exact Finset.card_le_card_of_injOn _ hmap hinj
  -- Step 5: 3 * W7.card <= 2 * (B7 gates).card via bipartite double counting
  have hW7_le : 3 * W7.card ≤ 2 * (B7 gates).card := by
    set E := (W7 ×ˢ B7 gates).filter (fun p => line p.1 ⊆ V gates (13 + p.2))
    have hleft : 3 * W7.card ≤ E.card := by
      have heq : E.card = ∑ w ∈ W7, ((B7 gates).filter (fun j => line w ⊆ V gates (13 + j))).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.card_filter]
      rw [heq]
      have hge3 : ∀ w ∈ W7, 3 ≤ ((B7 gates).filter (fun j => line w ⊆ V gates (13 + j))).card := by
        intro w hw
        have hwrem : w ∈ Wrem := (Finset.mem_sdiff.mp hw).1
        have hnot3 : ¬ (3 ≤ (Gw gates w).card) := by
          intro h3
          exact (Finset.mem_sdiff.mp hwrem).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ w, h3⟩)
        have hnot56 : ¬ (∃ j ∈ B56 gates, line w ⊆ V gates (13 + j)) := by
          intro h56
          exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_filter.mpr ⟨hwrem, h56⟩)
        rcases hline w with h3 | ⟨_, ht⟩
        · exact absurd h3 hnot3
        · rcases triple_split gates w ht with h56 | h3b
          · exact absurd h56 hnot56
          · exact h3b
      calc 3 * W7.card = ∑ _w ∈ W7, 3 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ w ∈ W7, ((B7 gates).filter (fun j => line w ⊆ V gates (13 + j))).card :=
          Finset.sum_le_sum hge3
    have hright : E.card ≤ 2 * (B7 gates).card := by
      have heq : E.card = ∑ j ∈ B7 gates, (W7.filter (fun w => line w ⊆ V gates (13 + j))).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.card_filter]
      rw [heq]
      have hle2 : ∀ j ∈ B7 gates, (W7.filter (fun w => line w ⊆ V gates (13 + j))).card ≤ 2 := by
        intro j hj
        have hc7 : (V gates (13 + j)).card = 7 := (Finset.mem_filter.mp hj).2
        have hsub : W7.filter (fun w => line w ⊆ V gates (13 + j)) ⊆
            Finset.univ.filter (fun w : Fin 13 => line w ⊆ V gates (13 + j)) := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, (Finset.mem_filter.mp hw).2⟩
        exact (Finset.card_le_card hsub).trans (lines_in_card7_le2 _ hc7)
      calc ∑ j ∈ B7 gates, (W7.filter (fun w => line w ⊆ V gates (13 + j))).card
          ≤ ∑ _j ∈ B7 gates, 2 := Finset.sum_le_sum hle2
        _ = 2 * (B7 gates).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  omega

end PEqualNP.Outside.L_meta_667_aux

theorem PEqualNP.Outside.L_meta_667 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin 13) (x : Fin 13 → Bool), (∀ i j k : Fin 13, x i = true → x j = true → x k = true → i = j ∨ j = k ∨ i = k) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)), x v = true)) → 39 ≤ gates.length :=
  fun gates out hvalid hcomp => PEqualNP.Outside.L_meta_667_aux.main_lb gates out hvalid hcomp
