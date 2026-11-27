import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3376
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

theorem val_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    val C x i = x.getD i false := wf_keep C.gates x i hi

theorem val_gate (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (x : List Bool) (hx : x.length = m)
    (k : ℕ) (hk : k < C.gates.length) :
    val C x (m + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => val C x i) := by
  have hG : gateAt C k = C.gates[k] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
  have g1 := gate_val C.gates x k hk
  rw [hx] at g1
  show (wf C.gates x).getD (m + k) false = _
  rw [g1, hG]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < m + k := by
    have := hrb k hk i
    rw [hG] at this
    exact this hi
  show _ = (wf C.gates x).getD i false
  rw [wire_take C.gates x k i (by rw [hx]; exact hlt) (le_of_lt hk)]

def RdBy (m : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k < C.gates.length, w' = m + k ∧ w ∈ (gateAt C k).inputs

open Classical in
noncomputable def cone (m : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun k => Relation.ReflTransGen (RdBy m C) (m + k) C.output)

theorem mem_cone (m : ℕ) (C : Circuit) (k : ℕ) :
    k ∈ cone m C ↔ k < C.gates.length ∧ Relation.ReflTransGen (RdBy m C) (m + k) C.output := by
  classical
  unfold cone
  simp only [Finset.mem_filter, Finset.mem_range]

theorem rd_lt (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (w w' : ℕ) (h : RdBy m C w w') :
    w < w' := by
  obtain ⟨k, hk, rfl, hw⟩ := h
  exact hrb k hk w hw

theorem rtg_le (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (w w' : ℕ)
    (h : Relation.ReflTransGen (RdBy m C) w w') : w ≤ w' := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (rd_lt m C hrb _ _ hbc))

theorem cone_le_out (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (k : ℕ) (hk : k ∈ cone m C) :
    m + k ≤ C.output :=
  rtg_le m C hrb _ _ ((mem_cone m C k).mp hk).2

theorem cone_closed (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (k : ℕ) (hk : k ∈ cone m C)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (hmw : m ≤ w) : w - m ∈ cone m C := by
  obtain ⟨hkl, hr⟩ := (mem_cone m C k).mp hk
  have hlt : w < m + k := hrb k hkl w hw
  refine (mem_cone m C _).mpr ⟨by omega, ?_⟩
  have e : m + (w - m) = w := by omega
  rw [e]
  exact Relation.ReflTransGen.head ⟨k, hkl, rfl, hw⟩ hr

theorem cone_read (m : ℕ) (C : Circuit) (j : ℕ) (hj : j ∈ cone m C) (hne : m + j ≠ C.output) :
    ∃ k ∈ cone m C, m + j ∈ (gateAt C k).inputs := by
  obtain ⟨_, hr⟩ := (mem_cone m C j).mp hj
  rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨k, hk, rfl, hw⟩, hc⟩
  · exact absurd h hne
  · exact ⟨k, (mem_cone m C k).mpr ⟨hk, hc⟩, hw⟩

theorem out_mem (m : ℕ) (C : Circuit) (h1 : m ≤ C.output) (h2 : C.output < m + C.gates.length) :
    C.output - m ∈ cone m C := by
  refine (mem_cone m C _).mpr ⟨by omega, ?_⟩
  have e : m + (C.output - m) = C.output := by omega
  rw [e]

theorem sum_len (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (G : Finset ℕ)
    (hG : ∀ k ∈ G, k < C.gates.length) :
    ∑ k ∈ G, (gateAt C k).inputs.length =
      ∑ w ∈ Finset.range (m + C.gates.length), readsIn C G w := by
  unfold readsIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hall : ∀ a ∈ ((gateAt C k).inputs : Multiset ℕ), a ∈ Finset.range (m + C.gates.length) := by
    intro a ha
    have ha' : a ∈ (gateAt C k).inputs := by simpa using ha
    have := hrb k (hG k hk) a ha'
    have := hG k hk
    rw [Finset.mem_range]; omega
  have := Multiset.sum_count_eq_card hall
  simp only [Multiset.coe_count, Multiset.coe_card] at this
  exact this.symm

theorem reads_out (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (j : ℕ) (hj : j ∈ cone m C)
    (hjo : m + j = C.output) : readsIn C (cone m C) (m + j) = 0 := by
  unfold readsIn
  apply Finset.sum_eq_zero
  intro k hk
  rw [List.count_eq_zero]
  intro hmem
  have h1 := cone_le_out m C hrb k hk
  have h2 := hrb k ((mem_cone m C k).mp hk).1 _ hmem
  omega

theorem reads_off (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (j : ℕ) (hj : j ∉ cone m C) :
    readsIn C (cone m C) (m + j) = 0 := by
  unfold readsIn
  apply Finset.sum_eq_zero
  intro k hk
  rw [List.count_eq_zero]
  intro hmem
  have := cone_closed m C hrb k hk (m + j) hmem (by omega)
  rw [show m + j - m = j by omega] at this
  exact hj this

theorem reads_pos (m : ℕ) (C : Circuit) (j : ℕ) (hj : j ∈ cone m C) (hne : m + j ≠ C.output) :
    1 ≤ readsIn C (cone m C) (m + j) := by
  obtain ⟨k, hk, hmem⟩ := cone_read m C j hj hne
  unfold readsIn
  calc 1 ≤ (gateAt C k).inputs.count (m + j) := List.count_pos_iff.mpr hmem
    _ ≤ _ := Finset.single_le_sum (f := fun k => (gateAt C k).inputs.count (m + j))
        (fun _ _ => Nat.zero_le _) hk

theorem cone_identity (m : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 m C)
    (h1 : m ≤ C.output) (h2 : C.output < m + C.gates.length) :
    (cone m C).card + 1 = ∑ w ∈ Finset.range m, readsIn C (cone m C) w +
      ∑ j ∈ cone m C, (readsIn C (cone m C) (m + j) - 1) := by
  obtain ⟨_, hrb, hlen⟩ := hC
  set K := cone m C with hK
  have hKb : ∀ k ∈ K, k < C.gates.length := fun k hk => ((mem_cone m C k).mp hk).1
  have hs := sum_len m C hrb K hKb
  have h2k : ∑ k ∈ K, (gateAt C k).inputs.length = 2 * K.card := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := hKb k hk
    have : gateAt C k = C.gates[k] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hk']
    rw [this, hlen _ (List.getElem_mem hk')]
    norm_num
  rw [Finset.range_add, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_range, Finset.mem_map, addLeftEmbedding_apply] at ha hb
    obtain ⟨b, _, rfl⟩ := hb; omega), Finset.sum_map] at hs
  simp only [addLeftEmbedding_apply] at hs
  have hsplit : ∑ j ∈ Finset.range C.gates.length, readsIn C K (m + j) =
      ∑ j ∈ K, readsIn C K (m + j) := by
    symm
    apply Finset.sum_subset
    · intro k hk; exact Finset.mem_range.mpr (hKb k hk)
    · intro j _ hj; exact reads_off m C hrb j hj
  rw [hsplit] at hs
  set o := C.output - m with ho
  have hoK : o ∈ K := out_mem m C h1 h2
  have hfix : ∑ j ∈ K, readsIn C K (m + j) + 1 =
      ∑ j ∈ K, (readsIn C K (m + j) - 1) + K.card := by
    rw [← Finset.add_sum_erase K _ hoK, ← Finset.add_sum_erase K _ hoK]
    have hro : readsIn C K (m + o) = 0 := reads_out m C hrb o hoK (by omega)
    rw [hro]
    have hrest : ∑ j ∈ K.erase o, readsIn C K (m + j) =
        ∑ j ∈ K.erase o, (readsIn C K (m + j) - 1) + (K.erase o).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have := reads_pos m C j (Finset.mem_of_mem_erase hj) (by
        intro e; apply Finset.ne_of_mem_erase hj; omega)
      rw [← hK] at this
      omega
    rw [hrest, Finset.card_erase_of_mem hoK]
    have : 1 ≤ K.card := Finset.card_pos.mpr ⟨o, hoK⟩
    omega
  omega

theorem agree (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (x x' : List Bool)
    (hx : x.length = m) (hx' : x'.length = m) (T : Finset ℕ) (A : ℕ → Prop)
    (hin : ∀ i < m, A i → x.getD i false = x'.getD i false)
    (hstep : ∀ k ∈ cone m C, k ∉ T → A (m + k) → ∀ w ∈ (gateAt C k).inputs, A w)
    (hT : ∀ k ∈ cone m C, k ∈ T → val C x (m + k) = val C x' (m + k)) :
    ∀ k ∈ cone m C, A (m + k) → val C x (m + k) = val C x' (m + k) := by
  have main : ∀ w, ∀ k, w = m + k → k ∈ cone m C → A (m + k) →
      val C x (m + k) = val C x' (m + k) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    intro k hw hk hA
    by_cases hkT : k ∈ T
    · exact hT k hk hkT
    have hkl : k < C.gates.length := ((mem_cone m C k).mp hk).1
    rw [val_gate m C hrb x hx k hkl, val_gate m C hrb x' hx' k hkl]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hAi := hstep k hk hkT hA i hi
    have hlt : i < m + k := hrb k hkl i hi
    by_cases him : i < m
    · rw [val_input C x i (by omega), val_input C x' i (by omega)]
      exact hin i him hAi
    · have hc := cone_closed m C hrb k hk i hi (by omega)
      have e : m + (i - m) = i := by omega
      have := ih i (by omega) (i - m) e.symm hc (by rw [e]; exact hAi)
      rw [e] at this
      exact this
  intro k hk hA
  exact main (m + k) k rfl hk hA

theorem eval_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem dep (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (h1 : m ≤ C.output)
    (h2 : C.output < m + C.gates.length) (i : ℕ) (hi : i < m)
    (h0 : readsIn C (cone m C) i = 0) (x x' : List Bool) (hx : x.length = m)
    (hx' : x'.length = m) (hagr : ∀ j < m, j ≠ i → x.getD j false = x'.getD j false) :
    C.eval x = C.eval x' := by
  have hno : ∀ k ∈ cone m C, i ∉ (gateAt C k).inputs := by
    intro k hk hmem
    unfold readsIn at h0
    have := (Finset.sum_eq_zero_iff.mp h0) k hk
    rw [List.count_eq_zero] at this
    exact this hmem
  have hoK := out_mem m C h1 h2
  have e : m + (C.output - m) = C.output := by omega
  have := agree m C hrb x x' hx hx' ∅ (fun w => w ≠ i) (fun j hj hA => hagr j hj hA)
    (fun k hk _ _ w hw => fun e => hno k hk (e ▸ hw)) (fun k _ hT => absurd hT (by simp))
    (C.output - m) hoK (by rw [e]; omega)
  rw [e] at this
  exact this

theorem inc_len (N : ℕ) (X Y : Finset (Fin N)) :
    (PEqualNP.GenericRejection.incidenceInput X Y).length = N + N := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem inc_pt (N : ℕ) (X Y : Finset (Fin N)) (i : ℕ) (hi : i < N) :
    (PEqualNP.GenericRejection.incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

theorem inc_ln (N : ℕ) (X Y : Finset (Fin N)) (i : ℕ) (hi : N ≤ i) (hi2 : i < N + N) :
    (PEqualNP.GenericRejection.incidenceInput X Y).getD i false =
      decide ((⟨i - N, by omega⟩ : Fin N) ∈ Y) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega)]
  have hl : (List.ofFn fun p : Fin N => decide (p ∈ X)).length = N := by simp
  rw [hl]
  have h3 : i - N < N := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h3]

theorem input_read (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (hpt : ∀ p : Fin N, ∃ l, p ∈ S l) (hln : ∀ l : Fin N, ∃ p, p ∈ S l) :
    ∀ i < N + N, 1 ≤ readsIn C (cone (N + N) C) i := by
  intro i hi
  by_contra hcon
  have h0 : readsIn C (cone (N + N) C) i = 0 := by omega
  have hrb := hC.2.1
  by_cases hiN : i < N
  · obtain ⟨l, hl⟩ := hpt ⟨i, hiN⟩
    have ha := hacc l ⟨i, hiN⟩ hl
    have hr := hrej ∅ {l} (by simp) (by intro l' _; simp)
    have := dep (N + N) C hrb h1 h2 i hi h0
      (PEqualNP.GenericRejection.incidenceInput {⟨i, hiN⟩} {l})
      (PEqualNP.GenericRejection.incidenceInput ∅ {l}) (inc_len _ _ _) (inc_len _ _ _) (by
        intro j hj hji
        by_cases hjN : j < N
        · rw [inc_pt _ _ _ j hjN, inc_pt _ _ _ j hjN]
          simp [Fin.ext_iff, hji]
        · rw [inc_ln _ _ _ j (by omega) hj, inc_ln _ _ _ j (by omega) hj])
    rw [ha, hr] at this
    exact absurd this (by simp)
  · obtain ⟨p, hp⟩ := hln ⟨i - N, by omega⟩
    have ha := hacc ⟨i - N, by omega⟩ p hp
    have hr := hrej {p} ∅ (by simp) (by intro l' hl'; simp at hl')
    have := dep (N + N) C hrb h1 h2 i hi h0
      (PEqualNP.GenericRejection.incidenceInput {p} {⟨i - N, by omega⟩})
      (PEqualNP.GenericRejection.incidenceInput {p} ∅) (inc_len _ _ _) (inc_len _ _ _) (by
        intro j hj hji
        by_cases hjN : j < N
        · rw [inc_pt _ _ _ j hjN, inc_pt _ _ _ j hjN]
        · rw [inc_ln _ _ _ j (by omega) hj, inc_ln _ _ _ j (by omega) hj]
          have hne : j - N ≠ i - N := by omega
          simp [Fin.ext_iff, hne])
    rw [ha, hr] at this
    exact absurd this (by simp)

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ (l : List ℕ) (f g : ℕ → Bool), (∀ i ∈ l, f i = true → g i = true) →
      op.eval (l.map f) = true → op.eval (l.map g) = true := by
  intro l f g hfg h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id] at h ⊢
    intro a ha
    exact hfg a ha (h a ha)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id] at h ⊢
    obtain ⟨a, ha, h1⟩ := h
    exact ⟨a, ha, hfg a ha h1⟩

theorem val_mono (m : ℕ) (C : Circuit) (hao : PEqualNP.EdgeOwnership.AndOrOnly C)
    (hrb : ReadsBack m C) (x x' : List Bool) (hx : x.length = m) (hx' : x'.length = m)
    (hle : ∀ i < m, x.getD i false = true → x'.getD i false = true) :
    ∀ w, val C x w = true → val C x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases hwm : w < m
  · rw [val_input C x w (by omega)] at hw
    rw [val_input C x' w (by omega)]
    exact hle w hwm hw
  by_cases hwg : w < m + C.gates.length
  · obtain ⟨k, rfl⟩ : ∃ k, w = m + k := ⟨w - m, by omega⟩
    have hk : k < C.gates.length := by omega
    rw [val_gate m C hrb x hx k hk] at hw
    rw [val_gate m C hrb x' hx' k hk]
    have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
      have : gateAt C k = C.gates[k] := by
        unfold gateAt; rw [List.getD_eq_getElem _ _ hk]
      rw [this]
      exact hao _ (List.getElem_mem hk)
    refine eval_mono _ hop _ _ _ ?_ hw
    intro i hi hv
    exact ih i (hrb k hk i hi) hv
  · exfalso
    have : val C x w = false := by
      show (C.wires x).getD w false = false
      have hl : (C.wires x).length = m + C.gates.length := by
        show (wf C.gates x).length = _
        rw [wf_len, hx]
      rw [List.getD_eq_default _ _ (by omega)]
    rw [this] at hw
    exact Bool.false_ne_true hw

theorem inc_le (N : ℕ) (X X' Y Y' : Finset (Fin N)) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    ∀ i < N + N, (PEqualNP.GenericRejection.incidenceInput X Y).getD i false = true →
      (PEqualNP.GenericRejection.incidenceInput X' Y').getD i false = true := by
  intro i hi h
  by_cases hin : i < N
  · rw [inc_pt N X Y i hin] at h
    rw [inc_pt N X' Y' i hin]
    simp only [decide_eq_true_eq] at h ⊢
    exact hX h
  · rw [inc_ln N X Y i (by omega) hi] at h
    rw [inc_ln N X' Y' i (by omega) hi]
    simp only [decide_eq_true_eq] at h ⊢
    exact hY h

theorem val_mono_inc (N : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (X X' Y Y' : Finset (Fin N)) (hX : X ⊆ X') (hY : Y ⊆ Y') (w : ℕ)
    (h : val C (PEqualNP.GenericRejection.incidenceInput X Y) w = true) :
    val C (PEqualNP.GenericRejection.incidenceInput X' Y') w = true :=
  val_mono (N + N) C hC.1 hC.2.1 _ _ (inc_len N X Y) (inc_len N X' Y') (inc_le N X X' Y Y' hX hY)
    w h

theorem eval_mono_inc (N : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (X X' Y Y' : Finset (Fin N)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true) :
    C.eval (PEqualNP.GenericRejection.incidenceInput X' Y') = true :=
  val_mono_inc N C hC X X' Y Y' hX hY C.output h

theorem uniq_reader (m : ℕ) (C : Circuit) (w : ℕ) (hf : readsIn C (cone m C) w = 1)
    (k k' : ℕ) (hk : k ∈ cone m C) (hw : w ∈ (gateAt C k).inputs) (hk' : k' ∈ cone m C)
    (hw' : w ∈ (gateAt C k').inputs) : k = k' := by
  by_contra hne
  have hsub : ({k, k'} : Finset ℕ) ⊆ cone m C := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hk
    · exact hk'
  have h1 := Finset.sum_le_sum_of_subset (f := fun j => (gateAt C j).inputs.count w) hsub
  rw [Finset.sum_pair hne] at h1
  have c1 : 1 ≤ (gateAt C k).inputs.count w := List.count_pos_iff.mpr hw
  have c2 : 1 ≤ (gateAt C k').inputs.count w := List.count_pos_iff.mpr hw'
  unfold readsIn at hf
  omega

theorem rtg_cone (m : ℕ) (C : Circuit) (w : ℕ) (hm : m ≤ w)
    (h : Relation.ReflTransGen (RdBy m C) w C.output) (hw : w < m + C.gates.length) :
    w - m ∈ cone m C := by
  refine (mem_cone m C _).mpr ⟨by omega, ?_⟩
  have e : m + (w - m) = w := by omega
  rw [e]; exact h

theorem reach (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (v t : ℕ)
    (hpath : Relation.ReflTransGen (RdBy m C) v t)
    (htout : Relation.ReflTransGen (RdBy m C) t C.output)
    (hsingle : ∀ w, Relation.ReflTransGen (RdBy m C) v w →
      Relation.ReflTransGen (RdBy m C) w C.output → w < t → readsIn C (cone m C) w = 1) :
    ∀ w, Relation.ReflTransGen (RdBy m C) v w → Relation.ReflTransGen (RdBy m C) w C.output →
      w ≤ t → Relation.ReflTransGen (RdBy m C) w t := by
  intro w hvw
  induction hvw with
  | refl => intro _ _; exact hpath
  | @tail w' w hvw' hstep ih =>
    intro hwo hwt
    have hlt : w' < w := rd_lt m C hrb _ _ hstep
    have ih' := ih (Relation.ReflTransGen.head hstep hwo) (by omega)
    rcases Relation.ReflTransGen.cases_head ih' with h | ⟨u, hu, hut⟩
    · omega
    · have hf := hsingle w' hvw' (Relation.ReflTransGen.head hstep hwo) (by omega)
      obtain ⟨k, hk, rfl, hkin⟩ := hstep
      obtain ⟨k', hk', rfl, hk'in⟩ := hu
      have hkK : k ∈ cone m C := (mem_cone m C k).mpr ⟨hk, hwo⟩
      have hk'K : k' ∈ cone m C := (mem_cone m C k').mpr ⟨hk', hut.trans htout⟩
      have := uniq_reader m C w' hf k k' hkK hkin hk'K hk'in
      subst this
      exact hut

theorem dominate (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (h1 : m ≤ C.output)
    (h2 : C.output < m + C.gates.length) (V : Finset ℕ) (j : ℕ) (hj : j ∈ cone m C)
    (hpath : ∀ v ∈ V, Relation.ReflTransGen (RdBy m C) v (m + j))
    (hsingle : ∀ v ∈ V, ∀ w, Relation.ReflTransGen (RdBy m C) v w →
      Relation.ReflTransGen (RdBy m C) w C.output → w < m + j → readsIn C (cone m C) w = 1)
    (x x' : List Bool) (hx : x.length = m) (hx' : x'.length = m)
    (hagr : ∀ i < m, i ∉ V → x.getD i false = x'.getD i false)
    (hmj : val C x (m + j) = val C x' (m + j)) : C.eval x = C.eval x' := by
  have hjo : Relation.ReflTransGen (RdBy m C) (m + j) C.output := ((mem_cone m C j).mp hj).2
  let A : ℕ → Prop := fun w => ¬ ∃ v ∈ V, Relation.ReflTransGen (RdBy m C) v w ∧ w < m + j
  have hin : ∀ i < m, A i → x.getD i false = x'.getD i false := by
    intro i hi hA
    apply hagr i hi
    intro hiV
    exact hA ⟨i, hiV, Relation.ReflTransGen.refl, by omega⟩
  have hstep : ∀ k ∈ cone m C, k ∉ ({j} : Finset ℕ) → A (m + k) →
      ∀ w ∈ (gateAt C k).inputs, A w := by
    intro k hk hkj hA w hw hbad
    obtain ⟨v, hv, hvw, hwlt⟩ := hbad
    have hkl : k < C.gates.length := ((mem_cone m C k).mp hk).1
    have hko : Relation.ReflTransGen (RdBy m C) (m + k) C.output := ((mem_cone m C k).mp hk).2
    have hstepk : RdBy m C w (m + k) := ⟨k, hkl, rfl, hw⟩
    have hwo : Relation.ReflTransGen (RdBy m C) w C.output := Relation.ReflTransGen.head hstepk hko
    have hr := reach m C hrb v (m + j) (hpath v hv) hjo (hsingle v hv) w hvw hwo (by omega)
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨u, hu, hut⟩
    · omega
    · have hf := hsingle v hv w hvw hwo hwlt
      obtain ⟨k', hk', rfl, hk'in⟩ := hu
      have hk'K : k' ∈ cone m C := (mem_cone m C k').mpr ⟨hk', hut.trans hjo⟩
      have := uniq_reader m C w hf k k' hk hw hk'K hk'in
      subst this
      have hle := rtg_le m C hrb _ _ hut
      have hne : k ≠ j := by
        intro e; apply hkj; simp [e]
      apply hA
      exact ⟨v, hv, Relation.ReflTransGen.tail hvw hstepk, by omega⟩
  have hT : ∀ k ∈ cone m C, k ∈ ({j} : Finset ℕ) → val C x (m + k) = val C x' (m + k) := by
    intro k _ hk
    simp only [Finset.mem_singleton] at hk
    subst hk; exact hmj
  have hoK := out_mem m C h1 h2
  have e : m + (C.output - m) = C.output := by omega
  have hAo : A (m + (C.output - m)) := by
    rintro ⟨v, _, _, hlt⟩
    have := cone_le_out m C hrb j hj
    omega
  have := agree m C hrb x x' hx hx' {j} A hin hstep hT (C.output - m) hoK hAo
  rw [e] at this
  exact this

def EP (m : ℕ) (C : Circuit) (v j : ℕ) : Prop :=
  j ∈ cone m C ∧ Relation.ReflTransGen (RdBy m C) v (m + j) ∧ readsIn C (cone m C) (m + j) ≠ 1

theorem ee_exists (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (h1 : m ≤ C.output)
    (h2 : C.output < m + C.gates.length) (v : ℕ) (hv : 1 ≤ readsIn C (cone m C) v) :
    ∃ j, EP m C v j := by
  have hoK := out_mem m C h1 h2
  have e : m + (C.output - m) = C.output := by omega
  refine ⟨C.output - m, hoK, ?_, ?_⟩
  · obtain ⟨k, hk, hkin⟩ : ∃ k ∈ cone m C, v ∈ (gateAt C k).inputs := by
      by_contra hno
      push_neg at hno
      unfold readsIn at hv
      have : ∑ j ∈ cone m C, (gateAt C j).inputs.count v = 0 :=
        Finset.sum_eq_zero (fun j hj => List.count_eq_zero.mpr (hno j hj))
      omega
    obtain ⟨hkl, hko⟩ := (mem_cone m C k).mp hk
    rw [e]
    exact Relation.ReflTransGen.head ⟨k, hkl, rfl, hkin⟩ hko
  · rw [e]
    have := reads_out m C hrb (C.output - m) hoK (by omega)
    rw [e] at this
    omega

open Classical in
noncomputable def ee (m : ℕ) (C : Circuit) (v : ℕ) : ℕ :=
  if h : ∃ j, EP m C v j then Nat.find h else 0

theorem ee_spec (m : ℕ) (C : Circuit) (v : ℕ) (h : ∃ j, EP m C v j) : EP m C v (ee m C v) := by
  classical
  unfold ee
  rw [dif_pos h]
  exact Nat.find_spec h

theorem ee_min (m : ℕ) (C : Circuit) (v j : ℕ) (hj : EP m C v j) : ee m C v ≤ j := by
  classical
  have h : ∃ j, EP m C v j := ⟨j, hj⟩
  unfold ee
  rw [dif_pos h]
  exact Nat.find_min' h hj

theorem ee_single (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (v : ℕ) (hv : v < m)
    (hf : readsIn C (cone m C) v = 1) :
    ∀ w, Relation.ReflTransGen (RdBy m C) v w → Relation.ReflTransGen (RdBy m C) w C.output →
      w < m + ee m C v → readsIn C (cone m C) w = 1 := by
  intro w hvw hwo hlt
  rcases Relation.ReflTransGen.cases_tail hvw with h | ⟨u, _, hu⟩
  · subst h; exact hf
  · obtain ⟨k, hk, rfl, _⟩ := hu
    have hkK : k ∈ cone m C := (mem_cone m C k).mpr ⟨hk, hwo⟩
    by_contra hne
    have := ee_min m C v k ⟨hkK, hvw, hne⟩
    omega

theorem val_out_range (m : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = m) (w : ℕ)
    (hw : m + C.gates.length ≤ w) : val C x w = false := by
  show (C.wires x).getD w false = false
  have hl : (C.wires x).length = m + C.gates.length := by
    show (wf C.gates x).length = _
    rw [wf_len, hx]
  rw [List.getD_eq_default _ _ (by omega)]

theorem indep (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (V : Finset ℕ) (x x' : List Bool)
    (hx : x.length = m) (hx' : x'.length = m)
    (hagr : ∀ i < m, i ∉ V → x.getD i false = x'.getD i false) :
    ∀ w, (∀ v ∈ V, ¬ Relation.ReflTransGen (RdBy m C) v w) → val C x w = val C x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hno
  by_cases hwm : w < m
  · rw [val_input C x w (by omega), val_input C x' w (by omega)]
    apply hagr w hwm
    intro hwV
    exact hno w hwV Relation.ReflTransGen.refl
  by_cases hwg : w < m + C.gates.length
  · obtain ⟨k, rfl⟩ : ∃ k, w = m + k := ⟨w - m, by omega⟩
    have hk : k < C.gates.length := by omega
    rw [val_gate m C hrb x hx k hk, val_gate m C hrb x' hx' k hk]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply ih i (hrb k hk i hi)
    intro v hv hvi
    exact hno v hv (Relation.ReflTransGen.tail hvi ⟨k, hk, rfl, hi⟩)
  · rw [val_out_range m C x hx w (by omega), val_out_range m C x' hx' w (by omega)]

theorem input_only (m : ℕ) (C : Circuit) (u w : ℕ) (hw : w < m)
    (h : Relation.ReflTransGen (RdBy m C) u w) : u = w := by
  rcases Relation.ReflTransGen.cases_tail h with e | ⟨c, _, hc⟩
  · exact e.symm
  · obtain ⟨k, _, rfl, _⟩ := hc
    omega

theorem lca (m : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 m C) (u v : ℕ) (hu : u < m)
    (hv : v < m) (huv : u ≠ v) (j : ℕ) (hj : j ∈ cone m C)
    (hju : Relation.ReflTransGen (RdBy m C) u (m + j))
    (hjv : Relation.ReflTransGen (RdBy m C) v (m + j)) :
    ∃ M, M ∈ cone m C ∧ M ≤ j ∧ Relation.ReflTransGen (RdBy m C) u (m + M) ∧
      Relation.ReflTransGen (RdBy m C) v (m + M) ∧
      ∃ a b, ((gateAt C M).inputs = [a, b] ∨ (gateAt C M).inputs = [b, a]) ∧
        Relation.ReflTransGen (RdBy m C) u a ∧ ¬ Relation.ReflTransGen (RdBy m C) v a ∧
        Relation.ReflTransGen (RdBy m C) v b ∧ ¬ Relation.ReflTransGen (RdBy m C) u b := by
  classical
  obtain ⟨_, hrb, hlen⟩ := hC
  have hex : ∃ M, M ∈ cone m C ∧ Relation.ReflTransGen (RdBy m C) u (m + M) ∧
      Relation.ReflTransGen (RdBy m C) v (m + M) := ⟨j, hj, hju, hjv⟩
  let M := Nat.find hex
  have hM : M ∈ cone m C ∧ Relation.ReflTransGen (RdBy m C) u (m + M) ∧
      Relation.ReflTransGen (RdBy m C) v (m + M) := Nat.find_spec hex
  have hMmin : ∀ M', M' ∈ cone m C → Relation.ReflTransGen (RdBy m C) u (m + M') →
      Relation.ReflTransGen (RdBy m C) v (m + M') → M ≤ M' :=
    fun M' h1 h2 h3 => Nat.find_min' hex ⟨h1, h2, h3⟩
  obtain ⟨hMK, hMu, hMv⟩ := hM
  have hMl : M < C.gates.length := ((mem_cone m C M).mp hMK).1
  have hMo : Relation.ReflTransGen (RdBy m C) (m + M) C.output := ((mem_cone m C M).mp hMK).2
  have common : ∀ w, Relation.ReflTransGen (RdBy m C) u w →
      Relation.ReflTransGen (RdBy m C) v w → w ∈ (gateAt C M).inputs → False := by
    intro w hw1 hw2 hwin
    have hlt : w < m + M := hrb M hMl w hwin
    by_cases hwm : w < m
    · have e1 := input_only m C u w hwm hw1
      have e2 := input_only m C v w hwm hw2
      exact huv (e1.trans e2.symm)
    · have hwK : w - m ∈ cone m C := cone_closed m C hrb M hMK w hwin (by omega)
      have e : m + (w - m) = w := by omega
      have := hMmin (w - m) hwK (by rw [e]; exact hw1) (by rw [e]; exact hw2)
      omega
  have hpre : ∀ t, t < m → Relation.ReflTransGen (RdBy m C) t (m + M) →
      ∃ a ∈ (gateAt C M).inputs, Relation.ReflTransGen (RdBy m C) t a := by
    intro t ht h
    rcases Relation.ReflTransGen.cases_tail h with e | ⟨c, hc, hcM⟩
    · omega
    · obtain ⟨k, hk, hkM, hcin⟩ := hcM
      have : k = M := by omega
      subst this
      exact ⟨c, hcin, hc⟩
  obtain ⟨a, ha, hua⟩ := hpre u hu hMu
  obtain ⟨b, hb, hvb⟩ := hpre v hv hMv
  have hva : ¬ Relation.ReflTransGen (RdBy m C) v a := fun h => common a hua h ha
  have hub : ¬ Relation.ReflTransGen (RdBy m C) u b := fun h => common b h hvb hb
  have hab : a ≠ b := by
    intro e; subst e; exact hva hvb
  have hl2 : (gateAt C M).inputs.length = 2 := by
    have : gateAt C M = C.gates[M] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hMl]
    rw [this]; exact hlen _ (List.getElem_mem hMl)
  refine ⟨M, hMK, hMmin j hj hju hjv, hMu, hMv, a, b, ?_, hua, hva, hvb, hub⟩
  match hL : (gateAt C M).inputs, hl2 with
  | [c, d], _ =>
    rw [hL] at ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · left; rfl
    · right; rfl
    · exact absurd rfl hab

theorem bstar_case (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l : p' ∈ S l) (hpl' : p ∈ S l')
    (hp'l' : p' ∉ S l') (hne : p' ≠ p)
    (M a b : ℕ) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (hval : ∀ X Y : Finset (Fin N),
      val C (PEqualNP.GenericRejection.incidenceInput X Y) M =
        op.eval [val C (PEqualNP.GenericRejection.incidenceInput X Y) a,
          val C (PEqualNP.GenericRejection.incidenceInput X Y) b])
    (hdom : ∀ X Y X' Y' : Finset (Fin N), (∀ r, r ≠ p → (r ∈ X ↔ r ∈ X')) →
      (∀ k, k ≠ l → (k ∈ Y ↔ k ∈ Y')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) M =
        val C (PEqualNP.GenericRejection.incidenceInput X' Y') M →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
        C.eval (PEqualNP.GenericRejection.incidenceInput X' Y'))
    (hA : ∀ X Y Y' : Finset (Fin N), (∀ k, k ≠ l → (k ∈ Y ↔ k ∈ Y')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) a =
        val C (PEqualNP.GenericRejection.incidenceInput X Y') a)
    (hB : ∀ X X' Y : Finset (Fin N), (∀ r, r ≠ p → (r ∈ X ↔ r ∈ X')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) b =
        val C (PEqualNP.GenericRejection.incidenceInput X' Y) b) : False := by
  classical
  have hl'l : l' ≠ l := by
    intro e; exact hp'l' (e ▸ hp'l)
  have r1 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := hacc l p hpl
  have r2 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) = false :=
    hrej _ _ (by simp) (by intro k hk; simp at hk)
  have r3 : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) = false :=
    hrej _ _ (by simp) (by intro k _; simp)
  rcases hop with rfl | rfl
  · have r4 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l'}) = true := hacc l' p hpl'
    have r5 : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) = false :=
      hrej _ _ (by simp) (by intro k _; simp)
    have r6 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} {l}) = true := hacc l p' hp'l
    have r7 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) = false :=
      hrej _ _ (by simp) (by intro k hk; simp at hk)
    have r8 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) = false := by
      apply hrej _ _ (by simp)
      intro k hk
      rw [Finset.mem_singleton] at hk
      subst hk
      exact Finset.disjoint_singleton_right.mpr hp'l'
    have hb1 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) b = true := by
      by_contra hb
      have hb0 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) b = false := by
        simpa using hb
      have hb0' : val C (PEqualNP.GenericRejection.incidenceInput {p} {l'}) b = false := by
        rw [hB {p} (∅ : Finset (Fin N)) {l'} (by intro r hr; simp [hr])]; exact hb0
      have := hdom {p} {l'} (∅ : Finset (Fin N)) {l'} (by intro r hr; simp [hr]) (by intro k _; rfl) (by
        rw [hval, hval]; simp [GateOp.eval, hb0, hb0'])
      rw [r4, r5] at this; exact absurd this (by simp)
    have ha1 : val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) a = true := by
      by_contra ha
      have ha0 : val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) a = false := by
        simpa using ha
      have ha0' : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l}) a = false := by
        rw [hA {p'} {l} (∅ : Finset (Fin N)) (by intro k hk; simp [hk])]; exact ha0
      have := hdom {p'} {l} {p'} (∅ : Finset (Fin N)) (by intro r _; rfl) (by intro k hk; simp [hk]) (by
        rw [hval, hval]; simp [GateOp.eval, ha0, ha0'])
      rw [r6, r7] at this; exact absurd this (by simp)
    have ha2 : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) a = true :=
      val_mono_inc N C hC _ _ _ _ (le_refl _) (by simp) a ha1
    have hb2 : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) b = true :=
      val_mono_inc N C hC _ _ _ _ (by simp) (le_refl _) b hb1
    have ha3 : val C (PEqualNP.GenericRejection.incidenceInput {p, p'} {l'}) a = true :=
      val_mono_inc N C hC _ _ _ _ (by simp) (le_refl _) a ha2
    have hb3 : val C (PEqualNP.GenericRejection.incidenceInput {p, p'} {l'}) b = true := by
      rw [← hB {p'} {p, p'} {l'} (by intro r hr; simp [hr])]; exact hb2
    have r9 : C.eval (PEqualNP.GenericRejection.incidenceInput {p, p'} {l'}) = true :=
      eval_mono_inc N C hC _ _ _ _ (by simp) (le_refl _) r4
    have := hdom {p'} {l'} {p, p'} {l'} (by intro r hr; simp [hr]) (by intro k _; rfl) (by
      rw [hval, hval]; simp [GateOp.eval, ha2, hb2, ha3, hb3])
    rw [r8, r9] at this; exact absurd this (by simp)
  · have ha0 : val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) a = false := by
      by_contra ha
      have ha1 : val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) a = true := by
        simpa using ha
      have ha1' : val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) a = true := by
        rw [← hA {p} (∅ : Finset (Fin N)) {l} (by intro k hk; simp [hk])]; exact ha1
      have := hdom {p} (∅ : Finset (Fin N)) {p} {l} (by intro r _; rfl) (by intro k hk; simp [hk]) (by
        rw [hval, hval]; simp [GateOp.eval, ha1, ha1'])
      rw [r2, r1] at this; exact absurd this (by simp)
    have ha00 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) a = false := by
      rw [hA (∅ : Finset (Fin N)) {l} (∅ : Finset (Fin N)) (by intro k hk; simp [hk])]
      by_contra ha
      have ha1 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) a = true := by
        simpa using ha
      have := val_mono_inc N C hC (∅ : Finset (Fin N)) {p} (∅ : Finset (Fin N)) (∅ : Finset (Fin N)) (by simp) (le_refl _) a ha1
      rw [ha0] at this; exact absurd this (by simp)
    have ha01 : val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) a = false := by
      rw [← hA {p} (∅ : Finset (Fin N)) {l} (by intro k hk; simp [hk])]; exact ha0
    have hbb : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) b =
        val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) b :=
      hB (∅ : Finset (Fin N)) {p} {l} (by intro r hr; simp [hr])
    have := hdom (∅ : Finset (Fin N)) {l} {p} {l} (by intro r hr; simp [hr]) (by intro k _; rfl) (by
      rw [hval, hval]; simp [GateOp.eval, ha00, ha01, hbb])
    rw [r3, r1] at this; exact absurd this (by simp)


theorem inc_agree (N : ℕ) (X Y X' Y' : Finset (Fin N)) (p l : Fin N)
    (hX : ∀ r, r ≠ p → (r ∈ X ↔ r ∈ X')) (hY : ∀ k, k ≠ l → (k ∈ Y ↔ k ∈ Y')) :
    ∀ i < N + N, i ∉ ({p.val, N + l.val} : Finset ℕ) →
      (PEqualNP.GenericRejection.incidenceInput X Y).getD i false =
        (PEqualNP.GenericRejection.incidenceInput X' Y').getD i false := by
  intro i hi hiV
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hiV
  by_cases hin : i < N
  · rw [inc_pt N X Y i hin, inc_pt N X' Y' i hin]
    have := hX ⟨i, hin⟩ (by intro e; apply hiV.1; rw [← e])
    simp [this]
  · rw [inc_ln N X Y i (by omega) hi, inc_ln N X' Y' i (by omega) hi]
    have := hY ⟨i - N, by omega⟩ (by intro e; apply hiV.2; rw [← e]; simp; omega)
    simp [this]

theorem bstar_chain (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l : p' ∈ S l) (hpl' : p ∈ S l')
    (hp'l' : p' ∉ S l') (hne : p' ≠ p)
    (hfp : readsIn C (cone (N + N) C) p.val = 1)
    (hfl : readsIn C (cone (N + N) C) (N + l.val) = 1) :
    ee (N + N) C p.val ≠ ee (N + N) C (N + l.val) := by
  intro hE
  have hrb := hC.2.1
  have exu := ee_exists (N + N) C hrb h1 h2 p.val (by omega)
  have exv := ee_exists (N + N) C hrb h1 h2 (N + l.val) (by omega)
  obtain ⟨hjK, hju, _⟩ := ee_spec (N + N) C p.val exu
  obtain ⟨_, hjv, _⟩ := ee_spec (N + N) C (N + l.val) exv
  rw [hE] at hjK hju
  obtain ⟨M, hMK, hMle, hMu, hMv, a, b, hab, hua, hva, hvb, hub⟩ :=
    lca (N + N) C hC p.val (N + l.val) (by omega) (by omega) (by omega) _ hjK hju hjv
  have hMl : M < C.gates.length := ((mem_cone (N + N) C M).mp hMK).1
  have hop : (gateAt C M).op = GateOp.and ∨ (gateAt C M).op = GateOp.or := by
    have : gateAt C M = C.gates[M] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hMl]
    rw [this]; exact hC.1 _ (List.getElem_mem hMl)
  refine bstar_case N S C hC hacc hrej p l p' l' hpl hp'l hpl' hp'l' hne (N + N + M) a b
    (gateAt C M).op hop ?_ ?_ ?_ ?_
  · intro X Y
    rw [val_gate (N + N) C hrb _ (inc_len N X Y) M hMl]
    rcases hab with h | h <;> rw [h]
    · rfl
    · rcases hop with ho | ho <;> rw [ho] <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
  · intro X Y X' Y' hX hY hval
    apply dominate (N + N) C hrb h1 h2 {p.val, N + l.val} M hMK
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hMu
      · exact hMv
    · intro v hv w hvw hwo hwlt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ee_single (N + N) C hrb _ (by omega) hfp w hvw hwo (by rw [hE] at *; omega)
      · exact ee_single (N + N) C hrb _ (by omega) hfl w hvw hwo (by omega)
    · exact inc_len N X Y
    · exact inc_len N X' Y'
    · exact inc_agree N X Y X' Y' p l hX hY
    · exact hval
  · intro X Y Y' hY
    apply indep (N + N) C hrb {N + l.val} _ _ (inc_len N X Y) (inc_len N X Y')
    · intro i hi hiV
      have := inc_agree N X Y X Y' p l (fun r _ => Iff.rfl) hY i hi
      by_cases hip : i = p.val
      · subst hip
        rw [inc_pt N X Y _ p.isLt, inc_pt N X Y' _ p.isLt]
      · apply this
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hip, by simpa using hiV⟩
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst hv; exact hva
  · intro X X' Y hX
    apply indep (N + N) C hrb {p.val} _ _ (inc_len N X Y) (inc_len N X' Y)
    · intro i hi hiV
      have := inc_agree N X Y X' Y p l hX (fun k _ => Iff.rfl) i hi
      by_cases hil : i = N + l.val
      · subst hil
        rw [inc_ln N X Y _ (by omega) hi, inc_ln N X' Y _ (by omega) hi]
      · apply this
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨by simpa using hiV, hil⟩
    · intro v hv
      simp only [Finset.mem_singleton] at hv
      subst hv; exact hub

theorem inj_mixed (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l' : p' ∈ S l') (w : ℕ)
    (hdom : ∀ X Y X' Y' : Finset (Fin N), (∀ r, r ≠ p → (r ∈ X ↔ r ∈ X')) →
      (∀ k, k ≠ l' → (k ∈ Y ↔ k ∈ Y')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) w =
        val C (PEqualNP.GenericRejection.incidenceInput X' Y') w →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
        C.eval (PEqualNP.GenericRejection.incidenceInput X' Y'))
    (hI : ∀ X X' Y Y' : Finset (Fin N), (∀ r, r ≠ p' → (r ∈ X ↔ r ∈ X')) →
      (∀ k, k ≠ l → (k ∈ Y ↔ k ∈ Y')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) w =
        val C (PEqualNP.GenericRejection.incidenceInput X' Y') w) : False := by
  classical
  have r1 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := hacc l p hpl
  have r2 : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) = false :=
    hrej _ _ (by simp) (by intro k _; simp)
  have r3 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) = true := hacc l' p' hp'l'
  have r4 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) = false :=
    hrej _ _ (by simp) (by intro k hk; simp at hk)
  have r5 : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l, l'}) = false := by
    apply hrej _ _ (by simp; exact le_trans (Finset.card_le_two) (by norm_num))
    intro k _; simp
  have s1 : val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) w = true := by
    by_contra h
    have h0 : val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) w = false := by simpa using h
    have h00 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) w = false := by
      by_contra h'
      have := val_mono_inc N C hC (∅ : Finset (Fin N)) {p} {l} {l} (by simp) (le_refl _) w
        (by simpa using h')
      rw [h0] at this; exact absurd this (by simp)
    have := hdom {p} {l} (∅ : Finset (Fin N)) {l} (by intro r hr; simp [hr]) (by intro k _; rfl)
      (by rw [h0, h00])
    rw [r1, r2] at this; exact absurd this (by simp)
  have s2 : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) w = true := by
    by_contra h
    have h0 : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) w = false := by simpa using h
    have h00 : val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w = false := by
      by_contra h'
      have := val_mono_inc N C hC {p'} {p'} (∅ : Finset (Fin N)) {l'} (le_refl _) (by simp) w
        (by simpa using h')
      rw [h0] at this; exact absurd this (by simp)
    have := hdom {p'} {l'} {p'} (∅ : Finset (Fin N)) (by intro r _; rfl) (by intro k hk; simp [hk])
      (by rw [h0, h00])
    rw [r3, r4] at this; exact absurd this (by simp)
  have s3 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w = true := by
    rw [← hI {p'} (∅ : Finset (Fin N)) {l'} {l'} (by intro r hr; simp [hr]) (by intro k _; rfl)]
    exact s2
  have s4 : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l, l'}) w = true :=
    val_mono_inc N C hC _ _ _ _ (le_refl _) (by simp) w s3
  have := hdom {p} {l} (∅ : Finset (Fin N)) {l, l'} (by intro r hr; simp [hr])
    (by intro k hk; simp [hk]) (by rw [s1, s4])
  rw [r1, r5] at this; exact absurd this (by simp)

theorem inj_pts (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l' : p' ∈ S l') (hp'l : p' ∉ S l) (w : ℕ)
    (hdom : ∀ X Y X' : Finset (Fin N), (∀ r, r ≠ p → r ≠ p' → (r ∈ X ↔ r ∈ X')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) w =
        val C (PEqualNP.GenericRejection.incidenceInput X' Y) w →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
        C.eval (PEqualNP.GenericRejection.incidenceInput X' Y))
    (hI : ∀ X Y Y' : Finset (Fin N), (∀ k, k ≠ l → k ≠ l' → (k ∈ Y ↔ k ∈ Y')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) w =
        val C (PEqualNP.GenericRejection.incidenceInput X Y') w) : False := by
  classical
  have r1 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := hacc l p hpl
  have r2 : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) = false :=
    hrej _ _ (by simp) (by intro k _; simp)
  have r3 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) = true := hacc l' p' hp'l'
  have r4 : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) = false :=
    hrej _ _ (by simp) (by intro k _; simp)
  have r5 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} {l}) = false := by
    apply hrej _ _ (by simp)
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    exact Finset.disjoint_singleton_right.mpr hp'l
  have eA : val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) w =
      val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro k hk _; simp [hk])
  have eB : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l}) w =
      val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro k hk _; simp [hk])
  have eB' : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) w =
      val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro k _ hk; simp [hk])
  have eZ : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro k hk _; simp [hk])
  have eZ' : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro k _ hk; simp [hk])
  have mA : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = true →
      val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) w = true :=
    val_mono_inc N C hC _ _ _ _ (by simp) (le_refl _) w
  have mB : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = true →
      val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w = true :=
    val_mono_inc N C hC _ _ _ _ (by simp) (le_refl _) w
  have hAB : val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) w ≠
      val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w := by
    intro h
    have := hdom {p} {l} {p'} (by intro r h1 h2; simp [h1, h2]) (by rw [eA, eB, h])
    rw [r1, r5] at this; exact absurd this (by simp)
  cases hA : val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) w <;>
    cases hB : val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w <;>
    rw [hA, hB] at hAB <;> simp at hAB
  · have hZ : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = false := by
      cases hz : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w
      · rfl
      · have := mA hz; rw [hA] at this; exact absurd this (by simp)
    have := hdom {p} {l} (∅ : Finset (Fin N)) (by intro r h1 _; simp [h1]) (by rw [eA, eZ, hA, hZ])
    rw [r1, r2] at this; exact absurd this (by simp)
  · have hZ : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = false := by
      cases hz : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w
      · rfl
      · have := mB hz; rw [hB] at this; exact absurd this (by simp)
    have := hdom {p'} {l'} (∅ : Finset (Fin N)) (by intro r _ h2; simp [h2]) (by rw [eB', eZ', hB, hZ])
    rw [r3, r4] at this; exact absurd this (by simp)

theorem inj_lns (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l' : p' ∈ S l') (hpl' : p ∉ S l') (w : ℕ)
    (hdom : ∀ X Y Y' : Finset (Fin N), (∀ k, k ≠ l → k ≠ l' → (k ∈ Y ↔ k ∈ Y')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) w =
        val C (PEqualNP.GenericRejection.incidenceInput X Y') w →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
        C.eval (PEqualNP.GenericRejection.incidenceInput X Y'))
    (hI : ∀ X X' Y : Finset (Fin N), (∀ r, r ≠ p → r ≠ p' → (r ∈ X ↔ r ∈ X')) →
      val C (PEqualNP.GenericRejection.incidenceInput X Y) w =
        val C (PEqualNP.GenericRejection.incidenceInput X' Y) w) : False := by
  classical
  have r1 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true := hacc l p hpl
  have r2 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) = false :=
    hrej _ _ (by simp) (by intro k hk; simp at hk)
  have r3 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) = true := hacc l' p' hp'l'
  have r4 : C.eval (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) = false :=
    hrej _ _ (by simp) (by intro k hk; simp at hk)
  have r5 : C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l'}) = false := by
    apply hrej _ _ (by simp)
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    exact Finset.disjoint_singleton_right.mpr hpl'
  have eA : val C (PEqualNP.GenericRejection.incidenceInput {p} {l}) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) w :=
    hI _ _ _ (by intro r hr _; simp [hr])
  have eB : val C (PEqualNP.GenericRejection.incidenceInput {p} {l'}) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w :=
    hI _ _ _ (by intro r hr _; simp [hr])
  have eB' : val C (PEqualNP.GenericRejection.incidenceInput {p'} {l'}) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w :=
    hI _ _ _ (by intro r _ hr; simp [hr])
  have eZ : val C (PEqualNP.GenericRejection.incidenceInput {p} (∅ : Finset (Fin N))) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro r hr _; simp [hr])
  have eZ' : val C (PEqualNP.GenericRejection.incidenceInput {p'} (∅ : Finset (Fin N))) w =
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w :=
    hI _ _ _ (by intro r _ hr; simp [hr])
  have mA : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = true →
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) w = true :=
    val_mono_inc N C hC _ _ _ _ (le_refl _) (by simp) w
  have mB : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = true →
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w = true :=
    val_mono_inc N C hC _ _ _ _ (le_refl _) (by simp) w
  have hAB : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) w ≠
      val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w := by
    intro h
    have := hdom {p} {l} {l'} (by intro k h1 h2; simp [h1, h2]) (by rw [eA, eB, h])
    rw [r1, r5] at this; exact absurd this (by simp)
  cases hA : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l}) w <;>
    cases hB : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) {l'}) w <;>
    rw [hA, hB] at hAB <;> simp at hAB
  · have hZ : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = false := by
      cases hz : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w
      · rfl
      · have := mA hz; rw [hA] at this; exact absurd this (by simp)
    have := hdom {p} {l} (∅ : Finset (Fin N)) (by intro k h1 _; simp [h1]) (by rw [eA, eZ, hA, hZ])
    rw [r1, r2] at this; exact absurd this (by simp)
  · have hZ : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w = false := by
      cases hz : val C (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) (∅ : Finset (Fin N))) w
      · rfl
      · have := mB hz; rw [hB] at this; exact absurd this (by simp)
    have := hdom {p'} {l'} (∅ : Finset (Fin N)) (by intro k _ h2; simp [h2]) (by rw [eB', eZ', hB, hZ])
    rw [r3, r4] at this; exact absurd this (by simp)


theorem inc_agreeV (N : ℕ) (X Y X' Y' : Finset (Fin N)) (V : Finset ℕ)
    (hX : ∀ r : Fin N, r.val ∉ V → (r ∈ X ↔ r ∈ X'))
    (hY : ∀ k : Fin N, N + k.val ∉ V → (k ∈ Y ↔ k ∈ Y')) :
    ∀ i < N + N, i ∉ V →
      (PEqualNP.GenericRejection.incidenceInput X Y).getD i false =
        (PEqualNP.GenericRejection.incidenceInput X' Y').getD i false := by
  intro i hi hiV
  by_cases hin : i < N
  · rw [inc_pt N X Y i hin, inc_pt N X' Y' i hin]
    have := hX ⟨i, hin⟩ hiV
    simp [this]
  · rw [inc_ln N X Y i (by omega) hi, inc_ln N X' Y' i (by omega) hi]
    have := hY ⟨i - N, by omega⟩ (by simp only; rw [show N + (i - N) = i by omega]; exact hiV)
    simp [this]

theorem not_reach (m : ℕ) (C : Circuit) (u v w0 : ℕ) (hu : EP m C u w0)
    (hlt : w0 < ee m C v) : ¬ Relation.ReflTransGen (RdBy m C) v (m + w0) := by
  intro h
  have := ee_min m C v w0 ⟨hu.1, h, hu.2.2⟩
  omega

theorem dom_pair (N : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length) (u v : ℕ)
    (hu : u < N + N) (hv : v < N + N)
    (hfu : readsIn C (cone (N + N) C) u = 1) (hfv : readsIn C (cone (N + N) C) v = 1)
    (hE : ee (N + N) C u = ee (N + N) C v) (X Y X' Y' : Finset (Fin N))
    (hX : ∀ r : Fin N, r.val ∉ ({u, v} : Finset ℕ) → (r ∈ X ↔ r ∈ X'))
    (hY : ∀ k : Fin N, N + k.val ∉ ({u, v} : Finset ℕ) → (k ∈ Y ↔ k ∈ Y'))
    (hval : val C (PEqualNP.GenericRejection.incidenceInput X Y) (N + N + ee (N + N) C u) =
      val C (PEqualNP.GenericRejection.incidenceInput X' Y') (N + N + ee (N + N) C u)) :
    C.eval (PEqualNP.GenericRejection.incidenceInput X Y) =
      C.eval (PEqualNP.GenericRejection.incidenceInput X' Y') := by
  have hrb := hC.2.1
  have exu := ee_exists (N + N) C hrb h1 h2 u (by omega)
  have exv := ee_exists (N + N) C hrb h1 h2 v (by omega)
  obtain ⟨hjK, hju, _⟩ := ee_spec (N + N) C u exu
  obtain ⟨_, hjv, _⟩ := ee_spec (N + N) C v exv
  rw [← hE] at hjv
  apply dominate (N + N) C hrb h1 h2 {u, v} (ee (N + N) C u) hjK
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hju
    · exact hjv
  · intro t ht w hvw hwo hwlt
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ee_single (N + N) C hrb _ hu hfu w hvw hwo hwlt
    · exact ee_single (N + N) C hrb _ hv hfv w hvw hwo (by rw [← hE]; exact hwlt)
  · exact inc_len N X Y
  · exact inc_len N X' Y'
  · exact inc_agreeV N X Y X' Y' {u, v} hX hY
  · exact hval

theorem indep_pair (N : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length) (u a b : ℕ)
    (hu : u < N + N) (hfu : readsIn C (cone (N + N) C) u = 1)
    (ha : ee (N + N) C u < ee (N + N) C a) (hb : ee (N + N) C u < ee (N + N) C b)
    (X Y X' Y' : Finset (Fin N))
    (hX : ∀ r : Fin N, r.val ∉ ({a, b} : Finset ℕ) → (r ∈ X ↔ r ∈ X'))
    (hY : ∀ k : Fin N, N + k.val ∉ ({a, b} : Finset ℕ) → (k ∈ Y ↔ k ∈ Y')) :
    val C (PEqualNP.GenericRejection.incidenceInput X Y) (N + N + ee (N + N) C u) =
      val C (PEqualNP.GenericRejection.incidenceInput X' Y') (N + N + ee (N + N) C u) := by
  have hrb := hC.2.1
  have exu := ee_exists (N + N) C hrb h1 h2 u (by omega)
  have hEP := ee_spec (N + N) C u exu
  apply indep (N + N) C hrb {a, b} _ _ (inc_len N X Y) (inc_len N X' Y')
    (inc_agreeV N X Y X' Y' {a, b} hX hY)
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact not_reach (N + N) C u t _ hEP ha
  · exact not_reach (N + N) C u t _ hEP hb


theorem mixed_chain (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l' : p' ∈ S l')
    (hfp : readsIn C (cone (N + N) C) p.val = 1)
    (hfl' : readsIn C (cone (N + N) C) (N + l'.val) = 1)
    (hE : ee (N + N) C p.val = ee (N + N) C (N + l'.val))
    (ha : ee (N + N) C p.val < ee (N + N) C p'.val)
    (hb : ee (N + N) C p.val < ee (N + N) C (N + l.val)) : False := by
  apply inj_mixed N S C hC hacc hrej p l p' l' hpl hp'l' (N + N + ee (N + N) C p.val)
  · intro X Y X' Y' hX hY hval
    apply dom_pair N C hC h1 h2 p.val (N + l'.val) (by omega) (by omega) hfp hfl' hE X Y X' Y'
      _ _ hval
    · intro r hr
      apply hX r
      intro e; apply hr; simp [e]
    · intro k hk
      apply hY k
      intro e; apply hk; simp [e]
  · intro X X' Y Y' hX hY
    apply indep_pair N C hC h1 h2 p.val p'.val (N + l.val) (by omega) hfp ha hb
    · intro r hr
      apply hX r
      intro e; apply hr; simp [e]
    · intro k hk
      apply hY k
      intro e; apply hk; simp [e]

theorem pts_chain (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l' : p' ∈ S l') (hp'l : p' ∉ S l)
    (hfp : readsIn C (cone (N + N) C) p.val = 1)
    (hfp' : readsIn C (cone (N + N) C) p'.val = 1)
    (hE : ee (N + N) C p.val = ee (N + N) C p'.val)
    (ha : ee (N + N) C p.val < ee (N + N) C (N + l.val))
    (hb : ee (N + N) C p.val < ee (N + N) C (N + l'.val)) : False := by
  apply inj_pts N S C hC hacc hrej p l p' l' hpl hp'l' hp'l (N + N + ee (N + N) C p.val)
  · intro X Y X' hX hval
    apply dom_pair N C hC h1 h2 p.val p'.val (by omega) (by omega) hfp hfp' hE X Y X' Y
      _ _ hval
    · intro r hr
      apply hX r
      · intro e; apply hr; simp [e]
      · intro e; apply hr; simp [e]
    · intro k _; exact Iff.rfl
  · intro X Y Y' hY
    apply indep_pair N C hC h1 h2 p.val (N + l.val) (N + l'.val) (by omega) hfp ha hb
    · intro r _; exact Iff.rfl
    · intro k hk
      apply hY k
      · intro e; apply hk; simp [e]
      · intro e; apply hk; simp [e]

theorem lns_chain (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 →
      PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l p' l' : Fin N) (hpl : p ∈ S l) (hp'l' : p' ∈ S l') (hpl' : p ∉ S l')
    (hfl : readsIn C (cone (N + N) C) (N + l.val) = 1)
    (hfl' : readsIn C (cone (N + N) C) (N + l'.val) = 1)
    (hE : ee (N + N) C (N + l.val) = ee (N + N) C (N + l'.val))
    (ha : ee (N + N) C (N + l.val) < ee (N + N) C p.val)
    (hb : ee (N + N) C (N + l.val) < ee (N + N) C p'.val) : False := by
  apply inj_lns N S C hC hacc hrej p l p' l' hpl hp'l' hpl' (N + N + ee (N + N) C (N + l.val))
  · intro X Y Y' hY hval
    apply dom_pair N C hC h1 h2 (N + l.val) (N + l'.val) (by omega) (by omega) hfl hfl' hE
      X Y X Y' _ _ hval
    · intro r _; exact Iff.rfl
    · intro k hk
      apply hY k
      · intro e; apply hk; simp [e]
      · intro e; apply hk; simp [e]
  · intro X X' Y hX
    apply indep_pair N C hC h1 h2 (N + l.val) p.val p'.val (by omega) hfl ha hb
    · intro r hr
      apply hX r
      · intro e; apply hr; simp [e]
      · intro e; apply hr; simp [e]
    · intro k _; exact Iff.rfl

end PEqualNP.Outside.L_meta_3376

namespace PEqualNP.Outside.L_meta_3376.Asm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_3376

theorem inj_assembly (N : ℕ) (K : Finset ℕ) (r : ℕ → ℕ) (e : ℕ → ℕ) (σ : Fin N → Fin N)
    (top : ℕ)
    (he : ∀ v, r v = 1 → e v ∈ K ∧ e v ≤ top ∧ (e v ≠ top → 2 ≤ r (N + N + e v)))
    (hb : ∀ l : Fin N, r (N + l.val) = 1 → r (σ l).val = 1 → e (N + l.val) ≠ e (σ l).val)
    (hi : ∀ l l' : Fin N, r (N + l.val) = 1 → r (σ l).val = 1 → r (N + l'.val) = 1 →
      r (σ l').val = 1 →
      min (e (N + l.val)) (e (σ l).val) = min (e (N + l'.val)) (e (σ l').val) → l = l') :
    (Finset.univ.filter (fun l : Fin N => r (N + l.val) = 1 ∧ r (σ l).val = 1)).card ≤
      (K.filter (fun j => 2 ≤ r (N + N + j))).card := by
  apply Finset.card_le_card_of_injOn (fun l => min (e (N + l.val)) (e (σ l).val))
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Finset.mem_filter] at hl ⊢
    obtain ⟨h1, h2⟩ := hl
    have hb' := hb l h1 h2
    obtain ⟨a1, a2, a3⟩ := he _ h1
    obtain ⟨b1, b2, b3⟩ := he _ h2
    rcases le_total (e (N + l.val)) (e (σ l).val) with h | h
    · rw [min_eq_left h]
      exact ⟨a1, a3 (by omega)⟩
    · rw [min_eq_right h]
      exact ⟨b1, b3 (by omega)⟩
  · intro l hl l' hl' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      Finset.mem_filter] at hl hl'
    exact hi l l' hl.1 hl.2 hl'.1 hl'.2 heq


theorem ee_range (m : ℕ) (C : Circuit) (hrb : ReadsBack m C) (h1 : m ≤ C.output)
    (h2 : C.output < m + C.gates.length) (v : ℕ) (hv : readsIn C (cone m C) v = 1) :
    ee m C v ∈ cone m C ∧ ee m C v ≤ C.output - m ∧
      (ee m C v ≠ C.output - m → 2 ≤ readsIn C (cone m C) (m + ee m C v)) := by
  have hex := ee_exists m C hrb h1 h2 v (by omega)
  obtain ⟨hK, _, hne1⟩ := ee_spec m C v hex
  have hle := cone_le_out m C hrb _ hK
  refine ⟨hK, by omega, fun hne => ?_⟩
  have := reads_pos m C _ hK (by omega)
  omega

end PEqualNP.Outside.L_meta_3376.Asm

namespace PEqualNP.Outside.L_meta_3376
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem deg_le (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) (p : Fin N) :
    (Finset.univ.filter (fun l : Fin N => p ∈ S l)).card ≤ q + 1 := by
  classical
  set L := Finset.univ.filter (fun l : Fin N => p ∈ S l) with hL
  have hsub : L.biUnion (fun l => (S l).erase p) ⊆ Finset.univ.erase p := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_erase] at hx
    obtain ⟨_, _, hx, _⟩ := hx
    exact Finset.mem_erase.mpr ⟨hx, Finset.mem_univ _⟩
  have hdisj : (L : Set (Fin N)).PairwiseDisjoint (fun l => (S l).erase p) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hL] at hi hj
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_erase] at hxi hxj
    obtain ⟨l, _, hl⟩ := hU p x (Ne.symm hxi.1)
    exact hij ((hl i ⟨hi, hxi.2⟩).trans (hl j ⟨hj, hxj.2⟩).symm)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at hcard
  have hterm : ∀ l ∈ L, ((S l).erase p).card = q := by
    intro l hl
    simp only [hL, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.card_erase_of_mem hl, hS l]
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem
    (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin] at hcard
  have h1 : N - 1 = (q + 1) * q := by
    rw [hN, Nat.add_sub_cancel]; ring
  rw [h1] at hcard
  exact Nat.le_of_mul_le_mul_right hcard hq

theorem hall_lines (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) :
    ∃ σ : Fin N → Fin N, Function.Injective σ ∧ ∀ l, σ l ∈ S l := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp
  intro B
  set U := B.biUnion S with hUdef
  have h1 : ∑ l ∈ B, (U ∩ S l).card = B.card * (q + 1) := by
    rw [Finset.sum_congr rfl (fun l hl => by
      rw [Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem S hl), hS]),
      Finset.sum_const, smul_eq_mul]
  have h2 : ∑ l ∈ B, (U ∩ S l).card = ∑ p ∈ U, (B.filter (fun l => p ∈ S l)).card := by
    simp_rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have h3 : ∑ p ∈ U, (B.filter (fun l => p ∈ S l)).card ≤ U.card * (q + 1) := by
    have := Finset.sum_le_card_nsmul U (fun p => (B.filter (fun l => p ∈ S l)).card) (q + 1)
      (fun p _ => le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ B))) (deg_le q N S hq hN hS hU p))
    simpa [smul_eq_mul] using this
  have h4 : B.card * (q + 1) ≤ U.card * (q + 1) := by omega
  exact Nat.le_of_mul_le_mul_right h4 (Nat.succ_pos q)

theorem count_split (N : ℕ) (σ : Fin N → Fin N) (hσ : Function.Injective σ)
    (P Q : Fin N → Prop) [DecidablePred P] [DecidablePred Q] :
    (Finset.univ.filter P).card + (Finset.univ.filter Q).card ≤
      N + (Finset.univ.filter (fun l => Q l ∧ P (σ l))).card := by
  classical
  have hbij : Function.Bijective σ := Finite.injective_iff_bijective.mp hσ
  have e1 : (Finset.univ.filter P).card = (Finset.univ.filter (fun l => P (σ l))).card := by
    have : Finset.univ.filter P = (Finset.univ.filter (fun l => P (σ l))).map ⟨σ, hσ⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hp
        obtain ⟨l, rfl⟩ := hbij.2 p
        exact ⟨l, hp, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact hl
    rw [this, Finset.card_map]
  rw [e1]
  have e2 := Finset.card_union_add_card_inter (Finset.univ.filter (fun l => P (σ l)))
    (Finset.univ.filter Q)
  have e3 : (Finset.univ.filter (fun l => P (σ l)) ∪ Finset.univ.filter Q).card ≤ N := by
    calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
      _ = N := by simp
  have e4 : Finset.univ.filter (fun l => P (σ l)) ∩ Finset.univ.filter Q =
      Finset.univ.filter (fun l => Q l ∧ P (σ l)) := by
    ext l; simp [and_comm]
  rw [e4] at e2
  omega


theorem split_range (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range (N + N)).filter P).card =
      (Finset.univ.filter (fun p : Fin N => P p.val)).card +
        (Finset.univ.filter (fun l : Fin N => P (N + l.val))).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_range_add, Finset.sum_range (fun i => if P i then 1 else 0),
    Finset.sum_range (fun i => if P (N + i) then 1 else 0)]

theorem core_assembly (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1) (hS : ∀ l, (S l).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l)
    (r : ℕ → ℕ) (D : ℕ)
    (hinj : ∀ σ : Fin N → Fin N, Function.Injective σ → (∀ l, σ l ∈ S l) →
      (Finset.univ.filter (fun l : Fin N => r (N + l.val) = 1 ∧ r (σ l).val = 1)).card ≤ D) :
    ((Finset.range (N + N)).filter (fun w => r w = 1)).card ≤ N + D := by
  classical
  obtain ⟨σ, hσ, hσS⟩ := hall_lines q N S hq hN hS hU
  have h1 := hinj σ hσ hσS
  have h2 := count_split N σ hσ (fun p => r p.val = 1) (fun l => r (N + l.val) = 1)
  rw [split_range N (fun w => r w = 1)]
  omega


theorem wires_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem output_is_gate (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 → PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false) : N + N ≤ C.output := by
  by_contra hlt
  simp only [not_le] at hlt
  by_cases hp : C.output < N
  · have h := hrej {⟨C.output, hp⟩} ∅ (by simp) (by intro l hl; simp at hl)
    have e : C.eval (PEqualNP.GenericRejection.incidenceInput ({⟨C.output, hp⟩} : Finset (Fin N)) (∅ : Finset (Fin N))) = true := by
      unfold Circuit.eval Circuit.wires
      rw [wires_keep _ _ _ (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)]
      simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simp; exact hp)]
      simp [List.getElem?_ofFn, hp]
    rw [h] at e; exact absurd e (by simp)
  · have hl : C.output - N < N := by omega
    have h := hrej ∅ {⟨C.output - N, hl⟩} (by simp) (by intro l _; simp)
    have e : C.eval (PEqualNP.GenericRejection.incidenceInput (∅ : Finset (Fin N)) ({⟨C.output - N, hl⟩} : Finset (Fin N))) = true := by
      unfold Circuit.eval Circuit.wires
      rw [wires_keep _ _ _ (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)]
      have hge : (List.ofFn (fun p : Fin N => decide (p ∈ (∅ : Finset (Fin N))))).length ≤ C.output := by
        simp; omega
      simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right hge]
      have hlen : (List.ofFn (fun p : Fin N => decide (p ∈ (∅ : Finset (Fin N))))).length = N := by simp
      rw [hlen]
      simp [List.getElem?_ofFn, hl]
    rw [h] at e; exact absurd e (by simp)


theorem other_point (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q)
    (deg : ∀ l, (S l).card = q + 1) (l : Fin N) (p : Fin N) (hp : p ∈ S l) :
    ∃ p' ∈ S l, p' ≠ p :=
  Finset.exists_mem_ne (by rw [deg]; omega) p

theorem other_line (q N : ℕ) (S : Fin N → Finset (Fin N)) (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1) (deg : ∀ l, (S l).card = q + 1)
    (join : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) (l : Fin N) (p : Fin N)
    (hp : p ∈ S l) : ∃ l', l' ≠ l ∧ p ∈ S l' := by
  obtain ⟨r, hr⟩ : ∃ r, r ∉ S l := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : (Finset.univ : Finset (Fin N)) ⊆ S l := fun x _ => h x
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin, deg] at this
    have : q + 1 < q ^ 2 + q + 1 := by nlinarith
    omega
  have hne : p ≠ r := fun e => hr (e ▸ hp)
  obtain ⟨l', ⟨h1, h2⟩, _⟩ := join p r hne
  exact ⟨l', fun e => hr (e ▸ h2), h1⟩

theorem off_line (N : ℕ) (S : Fin N → Finset (Fin N))
    (join : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) (l l' p p' : Fin N)
    (hp : p ∈ S l) (hp' : p' ∈ S l) (hne : p' ≠ p) (hl : l' ≠ l) (hpl : p ∈ S l') :
    p' ∉ S l' := by
  intro h
  obtain ⟨m, _, hm⟩ := join p p' (Ne.symm hne)
  exact hl ((hm l' ⟨hpl, h⟩).trans (hm l ⟨hp, hp'⟩).symm)


theorem ee_ep (N : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length) (v : ℕ)
    (hv : 1 ≤ readsIn C (cone (N + N) C) v) : EP (N + N) C v (ee (N + N) C v) :=
  ee_spec _ _ _ (ee_exists _ _ hC.2.1 h1 h2 v hv)

theorem ep_D (N : ℕ) (C : Circuit) (v j : ℕ) (hEP : EP (N + N) C v j)
    (hj : N + N + j ≠ C.output) :
    j ∈ (cone (N + N) C).filter (fun j => 2 ≤ readsIn C (cone (N + N) C) (N + N + j)) := by
  obtain ⟨hK, _, hne⟩ := hEP
  have := reads_pos (N + N) C j hK hj
  exact Finset.mem_filter.mpr ⟨hK, by omega⟩

theorem lands_in_D (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1) (deg : ∀ l, (S l).card = q + 1)
    (join : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C) (h1 : N + N ≤ C.output)
    (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 → PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (p l : Fin N) (hpl : p ∈ S l)
    (hfp : readsIn C (cone (N + N) C) p.val = 1)
    (hfl : readsIn C (cone (N + N) C) (N + l.val) = 1) :
    min (ee (N + N) C p.val) (ee (N + N) C (N + l.val)) ∈
      (cone (N + N) C).filter (fun j => 2 ≤ readsIn C (cone (N + N) C) (N + N + j)) := by
  obtain ⟨p', hp'l, hne⟩ := other_point q N S hq deg l p hpl
  obtain ⟨l', hl'l, hpl'⟩ := other_line q N S hq hN deg join l p hpl
  have hoff := off_line N S join l l' p p' hpl hp'l hne hl'l hpl'
  have hneq := bstar_chain N S C hC h1 h2 hacc hrej p l p' l' hpl hp'l hpl' hoff hne hfp hfl
  have e1 := ee_ep N C hC h1 h2 p.val (by omega)
  have e2 := ee_ep N C hC h1 h2 (N + l.val) (by omega)
  have le1 := cone_le_out (N + N) C hC.2.1 _ e1.1
  have le2 := cone_le_out (N + N) C hC.2.1 _ e2.1
  rcases le_total (ee (N + N) C p.val) (ee (N + N) C (N + l.val)) with h | h
  · rw [min_eq_left h]
    apply ep_D N C _ _ e1
    have : ee (N + N) C p.val < ee (N + N) C (N + l.val) := lt_of_le_of_ne h hneq
    omega
  · rw [min_eq_right h]
    apply ep_D N C _ _ e2
    have : ee (N + N) C (N + l.val) < ee (N + N) C p.val := lt_of_le_of_ne h (Ne.symm hneq)
    omega

theorem hi_cases (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (join : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C) (h1 : N + N ≤ C.output)
    (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 → PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (σ : Fin N → Fin N) (hσ : Function.Injective σ) (hσS : ∀ l, σ l ∈ S l)
    (hb : ∀ l : Fin N, readsIn C (cone (N + N) C) (N + l.val) = 1 →
      readsIn C (cone (N + N) C) (σ l).val = 1 →
      ee (N + N) C (N + l.val) ≠ ee (N + N) C (σ l).val)
    (l l' : Fin N) (hfl : readsIn C (cone (N + N) C) (N + l.val) = 1)
    (hfp : readsIn C (cone (N + N) C) (σ l).val = 1)
    (hfl' : readsIn C (cone (N + N) C) (N + l'.val) = 1)
    (hfp' : readsIn C (cone (N + N) C) (σ l').val = 1)
    (hmin : min (ee (N + N) C (N + l.val)) (ee (N + N) C (σ l).val) =
      min (ee (N + N) C (N + l'.val)) (ee (N + N) C (σ l').val)) : l = l' := by
  by_contra hne
  have hpp : σ l ≠ σ l' := fun e => hne (hσ e)
  have hnotboth : ¬ (σ l' ∈ S l ∧ σ l ∈ S l') := by
    rintro ⟨h3, h4⟩
    obtain ⟨m0, _, hm⟩ := join (σ l) (σ l') hpp
    exact hne ((hm l ⟨hσS l, h3⟩).trans (hm l' ⟨h4, hσS l'⟩).symm)
  have hb1 := hb l hfl hfp
  have hb2 := hb l' hfl' hfp'
  rcases lt_or_gt_of_ne hb1 with c1 | c1 <;> rcases lt_or_gt_of_ne hb2 with c2 | c2
  · rw [min_eq_left (le_of_lt c1), min_eq_left (le_of_lt c2)] at hmin
    by_cases hx : σ l ∈ S l'
    · have hy : σ l' ∉ S l := fun h => hnotboth ⟨h, hx⟩
      exact lns_chain N S C hC h1 h2 hacc hrej (σ l') l' (σ l) l (hσS l') (hσS l) hy hfl' hfl
        hmin.symm (by omega) (by omega)
    · exact lns_chain N S C hC h1 h2 hacc hrej (σ l) l (σ l') l' (hσS l) (hσS l') hx hfl hfl'
        hmin (by omega) (by omega)
  · rw [min_eq_left (le_of_lt c1), min_eq_right (le_of_lt c2)] at hmin
    exact mixed_chain N S C hC h1 h2 hacc hrej (σ l') l' (σ l) l (hσS l') (hσS l) hfp' hfl
      hmin.symm (by omega) (by omega)
  · rw [min_eq_right (le_of_lt c1), min_eq_left (le_of_lt c2)] at hmin
    exact mixed_chain N S C hC h1 h2 hacc hrej (σ l) l (σ l') l' (hσS l) (hσS l') hfp hfl'
      hmin (by omega) (by omega)
  · rw [min_eq_right (le_of_lt c1), min_eq_right (le_of_lt c2)] at hmin
    by_cases hx : σ l' ∈ S l
    · have hy : σ l ∉ S l' := fun h => hnotboth ⟨hx, h⟩
      exact pts_chain N S C hC h1 h2 hacc hrej (σ l') l' (σ l) l (hσS l') (hσS l) hy hfp' hfp
        hmin.symm (by omega) (by omega)
    · exact pts_chain N S C hC h1 h2 hacc hrej (σ l) l (σ l') l' (hσS l) (hσS l') hx hfp hfp'
        hmin (by omega) (by omega)

theorem hinj_open (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1) (deg : ∀ l, (S l).card = q + 1)
    (join : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C) (h1 : N + N ≤ C.output)
    (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 → PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false)
    (σ : Fin N → Fin N) (hσ : Function.Injective σ) (hσS : ∀ l, σ l ∈ S l) :
    (Finset.univ.filter (fun l : Fin N => readsIn C (cone (N + N) C) (N + l.val) = 1 ∧
      readsIn C (cone (N + N) C) (σ l).val = 1)).card ≤
      ((cone (N + N) C).filter (fun j => 2 ≤ readsIn C (cone (N + N) C) (N + N + j))).card := by
  classical
  have hb : ∀ l : Fin N, readsIn C (cone (N + N) C) (N + l.val) = 1 →
      readsIn C (cone (N + N) C) (σ l).val = 1 →
      ee (N + N) C (N + l.val) ≠ ee (N + N) C (σ l).val := by
    intro l hfl hfp
    obtain ⟨p', hp'l, hne⟩ := other_point q N S hq deg l (σ l) (hσS l)
    obtain ⟨l', hl'l, hpl'⟩ := other_line q N S hq hN deg join l (σ l) (hσS l)
    have hoff := off_line N S join l l' (σ l) p' (hσS l) hp'l hne hl'l hpl'
    exact (bstar_chain N S C hC h1 h2 hacc hrej (σ l) l p' l' (hσS l) hp'l hpl' hoff hne hfp hfl).symm
  exact Asm.inj_assembly N (cone (N + N) C) (fun w => readsIn C (cone (N + N) C) w) (ee (N + N) C) σ
    (C.output - (N + N)) (fun v hv => Asm.ee_range (N + N) C hC.2.1 h1 h2 v hv) hb
    (fun l l' a b c e f => hi_cases q N S C join hC h1 h2 hacc hrej σ hσ hσS hb l l' a b c e f)

theorem core (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1) (deg : ∀ l, (S l).card = q + 1)
    (join : ∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l)
    (hC : PEqualNP.TopForm.IsAO2 (N + N) C) (h1 : N + N ≤ C.output)
    (h2 : C.output < N + N + C.gates.length)
    (hacc : PEqualNP.GenericRejection.RightOnIncidentPairs S C)
    (hrej : ∀ X Y : Finset (Fin N), X.card + Y.card ≤ 3 → PEqualNP.GenericRejection.IsFalseInput S X Y →
      C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = false) :
    ((Finset.range (N + N)).filter (fun w => readsIn C (cone (N + N) C) w = 1)).card ≤
      N + ((cone (N + N) C).filter (fun j => 2 ≤ readsIn C (cone (N + N) C) (N + N + j))).card := by
  classical
  apply core_assembly q N S hq hN deg join (fun w => readsIn C (cone (N + N) C) w)
  intro σ hσ hσS
  exact hinj_open q N S C hq hN deg join hC h1 h2 hacc hrej σ hσ hσS

theorem glue (N : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (N + N) C)
    (h1 : N + N ≤ C.output) (h2 : C.output < N + N + C.gates.length)
    (hread : ∀ i < N + N, 1 ≤ readsIn C (cone (N + N) C) i)
    (hcore : ((Finset.range (N + N)).filter (fun w => readsIn C (cone (N + N) C) w = 1)).card ≤
      N + ((cone (N + N) C).filter (fun j => 2 ≤ readsIn C (cone (N + N) C) (N + N + j))).card) :
    N + N + N ≤ C.size + 1 := by
  have hid := cone_identity (N + N) C hC h1 h2
  set K := cone (N + N) C with hK
  have hKsz : K.card ≤ C.size := by
    have : K ⊆ Finset.range C.gates.length := by
      intro k hk; exact Finset.mem_range.mpr ((mem_cone _ C k).mp hk).1
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    exact this
  have hA : 2 * (N + N) ≤ ∑ w ∈ Finset.range (N + N), readsIn C K w +
      ((Finset.range (N + N)).filter (fun w => readsIn C K w = 1)).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    calc 2 * (N + N) = ∑ w ∈ Finset.range (N + N), 2 := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro w hw
        have := hread w (Finset.mem_range.mp hw)
        split_ifs with h <;> omega
  have hD : ((K.filter (fun j => 2 ≤ readsIn C K (N + N + j)))).card ≤
      ∑ j ∈ K, (readsIn C K (N + N + j) - 1) := by
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro j _
    split_ifs with h <;> omega
  omega

end PEqualNP.Outside.L_meta_3376

open PEqualNP.Outside.L_meta_3376 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3376 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ) := by
  intro q N S C hq hN deg join hC hout hacc hrej
  have h1 := output_is_gate N S C hrej
  have hN3 : 2 ≤ N := by subst hN; nlinarith
  have hpt : ∀ p : Fin N, ∃ l, p ∈ S l := by
    intro p
    obtain ⟨r, _, hr⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset (Fin N)))
      (by rw [Finset.card_univ, Fintype.card_fin]; omega) p
    obtain ⟨l, ⟨hl, _⟩, _⟩ := join p r (Ne.symm hr)
    exact ⟨l, hl⟩
  have hln : ∀ l : Fin N, ∃ p, p ∈ S l := by
    intro l
    have : 0 < (S l).card := by rw [deg]; omega
    obtain ⟨p, hp⟩ := Finset.card_pos.mp this
    exact ⟨p, hp⟩
  have hread := input_read N S C hC h1 hout hacc hrej hpt hln
  have hcore := core q N S C hq hN deg join hC h1 hout hacc hrej
  exact glue N C hC h1 hout hread hcore
