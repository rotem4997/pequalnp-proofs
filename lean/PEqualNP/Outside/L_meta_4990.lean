import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4990_aux

-- evaluation toolkit copied from extra/submitted/L_meta_4846.lean; leaf_count, Reach, A, the star
-- lemmas and the count adapted from extra/submitted/L_meta_4803.lean (fixed plane made general)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def pr {n : ℕ} (u v : Fin n) : Fin n → Bool := fun c => decide (c = u ∨ c = v)
lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]


section cl

open Classical

-- abstract leaf count: a family closed under unions of two earlier members
lemma leaf_count {α : Type*} [DecidableEq α] (cls : ℕ → Prop) (T : ℕ → Finset α)
    (h : ∀ w, cls w → (T w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ cls a ∧ cls b ∧ T w = T a ∪ T b) :
    ∀ M (W : Finset ℕ), (∀ w ∈ W, w < M ∧ cls w) →
      (W.biUnion T).card ≤ W.card +
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)).card := by
  intro M
  induction M with
  | zero =>
    intro W hW
    have : W = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hW w hw).1 (by omega)
    subst this
    simp
  | succ M ih =>
    intro W hW
    have hmono : ∀ U U' : Finset α, U ⊆ U' →
        ((Finset.range M).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U)).card ≤
        ((Finset.range (M + 1)).filter (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ U')).card := by
      intro U U' hU
      apply Finset.card_le_card
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by omega, hk.2.1, hk.2.2.1, hk.2.2.2.trans hU⟩
    by_cases hM : M ∈ W
    · have hWe : W = insert M (W.erase M) := (Finset.insert_erase hM).symm
      have hW' : ∀ w ∈ W.erase M, w < M ∧ cls w := by
        intro w hw
        rw [Finset.mem_erase] at hw
        have := hW w hw.2
        exact ⟨by omega, this.2⟩
      have hnot : M ∉ W.erase M := Finset.notMem_erase M W
      have hcard : W.card = (W.erase M).card + 1 := by
        rw [Finset.card_erase_of_mem hM]
        have := Finset.card_pos.mpr ⟨M, hM⟩
        omega
      have hU : W.biUnion T = T M ∪ (W.erase M).biUnion T := by
        conv_lhs => rw [hWe]
        rw [Finset.biUnion_insert]
      by_cases h1 : (T M).card ≤ 1
      · have ih1 := ih (W.erase M) hW'
        have hsub : (W.erase M).biUnion T ⊆ W.biUnion T := by
          rw [hU]; exact Finset.subset_union_right
        have := hmono _ _ hsub
        have hu := Finset.card_union_le (T M) ((W.erase M).biUnion T)
        rw [hU] at this ⊢
        omega
      · rcases h M (hW M hM).2 with h2 | ⟨a, b, ha, hb, ca, cb, hT⟩
        · exact absurd h2 h1
        · set W2 := insert a (insert b (W.erase M)) with hW2
          have hW2' : ∀ w ∈ W2, w < M ∧ cls w := by
            intro w hw
            rw [hW2, Finset.mem_insert, Finset.mem_insert] at hw
            rcases hw with rfl | rfl | hw
            · exact ⟨ha, ca⟩
            · exact ⟨hb, cb⟩
            · exact hW' w hw
          have hU2 : W2.biUnion T = W.biUnion T := by
            rw [hW2, Finset.biUnion_insert, Finset.biUnion_insert, hU, hT, Finset.union_assoc]
          have hc2 : W2.card ≤ (W.erase M).card + 2 := by
            rw [hW2]
            have e1 := Finset.card_insert_le a (insert b (W.erase M))
            have e2 := Finset.card_insert_le b (W.erase M)
            omega
          have ih2 := ih W2 hW2'
          rw [hU2] at ih2
          have hsplit : (Finset.range (M + 1)).filter
              (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T) =
              insert M ((Finset.range M).filter
                (fun k => cls k ∧ 2 ≤ (T k).card ∧ T k ⊆ W.biUnion T)) := by
            rw [Finset.range_add_one, Finset.filter_insert, if_pos]
            refine ⟨(hW M hM).2, by omega, ?_⟩
            rw [hU]; exact Finset.subset_union_left
          rw [hsplit, Finset.card_insert_of_notMem (by simp)]
          omega
    · have hW' : ∀ w ∈ W, w < M ∧ cls w := by
        intro w hw
        have := hW w hw
        have hne : w ≠ M := fun he => hM (he ▸ hw)
        exact ⟨by omega, this.2⟩
      have := ih W hW'
      have := hmono (W.biUnion T) (W.biUnion T) le_rfl
      omega


section circ

variable (n : ℕ) (C : Circuit)

lemma gv (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (h1 : n ≤ w) (h2 : w < n + C.gates.length) :
    ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧
      ((gateAt C (w - n)).op = GateOp.and ∨ (gateAt C (w - n)).op = GateOp.or) ∧
      ∀ x : Fin n → Bool, val C.gates x w =
        (gateAt C (w - n)).op.eval [val C.gates x a, val C.gates x b] := by
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  have e : n + k - n = k := by omega
  rw [e]
  obtain ⟨hAO, hRB, hL⟩ := hC
  have hmem := List.getElem_mem hk
  have h2 := hL _ hmem
  have hop := hAO _ hmem
  rw [← gateAt_eq C k hk] at h2 hop
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp h2
  have ha := hRB k hk a (by rw [hab]; simp)
  have hb := hRB k hk b (by rw [hab]; simp)
  refine ⟨a, b, hab, ha, hb, hop, fun x => ?_⟩
  rw [val_gate C.gates x k hk, ← gateAt_eq C k hk, hab]
  simp [ha, hb]

lemma ev_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

lemma ev_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

def S (w : ℕ) : Finset (Fin n) := Finset.univ.filter (fun v => val C.gates (eof v) w = true)

lemma mem_S (w : ℕ) (v : Fin n) : v ∈ S n C w ↔ val C.gates (eof v) w = true := by simp [S]

lemma S_inp (w : ℕ) (hw : w < n) : S n C w = {⟨w, hw⟩} := by
  ext v
  rw [mem_S, val_lt C.gates _ w hw]
  simp only [eof, decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma S_or (a b w : ℕ)
    (hv : ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) :
    S n C w = S n C a ∪ S n C b := by
  ext v
  simp only [Finset.mem_union, mem_S, hv, Bool.or_eq_true]

def Z (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ ∀ v : Fin n, val C.gates (eof v) w = false

lemma z_struct (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (hz : Z n C w) :
    (gateAt C (w - n)).op = GateOp.and ∨ ((gateAt C (w - n)).op = GateOp.or ∧
      ∃ a b, (gateAt C (w - n)).inputs = [a, b] ∧ a < w ∧ b < w ∧ Z n C a ∧ Z n C b ∧
        ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b)) := by
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨a, b, hab, ha, hb, hop, hv⟩ := gv n C hC w h1 h2
  rcases hop with hop | hop
  · exact Or.inl hop
  · right
    have hv' : ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
      intro x; rw [hv x, hop, ev_or]
    have hza : ∀ c, c < w → (∀ v : Fin n, val C.gates (eof v) w = false → val C.gates (eof v) c = false) →
        Z n C c := by
      intro c hc hcv
      refine ⟨?_, by omega, fun v => hcv v (h3 v)⟩
      by_contra hlt
      push_neg at hlt
      have := hcv ⟨c, hlt⟩ (h3 _)
      rw [val_lt C.gates _ c hlt] at this
      simp [eof] at this
    refine ⟨hop, a, b, hab, ha, hb, hza a ha ?_, hza b hb ?_, hv'⟩
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.1
    · intro v hv0; rw [hv'] at hv0; simp only [Bool.or_eq_false_iff] at hv0; exact hv0.2

inductive Reach : ℕ → ℕ → Prop
  | self (w : ℕ) : n ≤ w → w < n + C.gates.length → (gateAt C (w - n)).op = GateOp.and →
      Reach w w
  | up (j w a : ℕ) : n ≤ w → w < n + C.gates.length → (gateAt C (w - n)).op = GateOp.or →
      a ∈ (gateAt C (w - n)).inputs → Reach j a → Reach j w

lemma reach_and (hC : PEqualNP.TopForm.IsAO2 n C) (j w : ℕ) (h : Reach n C j w) :
    n ≤ j ∧ j < n + C.gates.length ∧ (gateAt C (j - n)).op = GateOp.and ∧ j ≤ w := by
  induction h with
  | self h1 h2 h3 => exact ⟨h1, h2, h3, le_rfl⟩
  | up w a h1 h2 _ h4 _ ih =>
    obtain ⟨a', b', hab, ha, hb, _, _⟩ := gv n C hC w h1 h2
    rw [hab] at h4
    have : a < w := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
      rcases h4 with rfl | rfl <;> assumption
    exact ⟨ih.1, ih.2.1, ih.2.2.1, by omega⟩

lemma reach_val (hC : PEqualNP.TopForm.IsAO2 n C) (j w : ℕ) (h : Reach n C j w) :
    ∀ x : Fin n → Bool, val C.gates x j = true → val C.gates x w = true := by
  induction h with
  | self _ _ _ => exact fun x hx => hx
  | up w a h1 h2 h3 h4 _ ih =>
    intro x hx
    obtain ⟨a', b', hab, _, _, _, hv⟩ := gv n C hC w h1 h2
    rw [hab] at h4
    rw [hv x, h3, ev_or, Bool.or_eq_true]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
    rcases h4 with rfl | rfl
    · exact Or.inl (ih x hx)
    · exact Or.inr (ih x hx)

lemma z_sem (hC : PEqualNP.TopForm.IsAO2 n C) : ∀ w, Z n C w → ∀ x : Fin n → Bool,
    val C.gates x w = true → ∃ j, Reach n C j w ∧ val C.gates x j = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz x hx
    rcases z_struct n C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, hv⟩
    · exact ⟨w, Reach.self w hz.1 hz.2.1 hop, hx⟩
    · rw [hv, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · obtain ⟨j, hj, hjx⟩ := ih a ha za x hx
        exact ⟨j, Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩
      · obtain ⟨j, hj, hjx⟩ := ih b hb zb x hx
        exact ⟨j, Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) hj, hjx⟩

lemma reach_inv (j w : ℕ) (h : Reach n C j w) :
    (j = w ∧ n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.and) ∨
    (n ≤ w ∧ w < n + C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or ∧
      ∃ a ∈ (gateAt C (w - n)).inputs, Reach n C j a) := by
  cases h
  · exact Or.inl ⟨rfl, by assumption, by assumption, by assumption⟩
  · exact Or.inr ⟨by assumption, by assumption, by assumption, _, by assumption, by assumption⟩

noncomputable def A (w : ℕ) : Finset ℕ :=
  (Finset.range (n + C.gates.length)).filter (fun j => Reach n C j w)

lemma mem_A (hC : PEqualNP.TopForm.IsAO2 n C) (j w : ℕ) : j ∈ A n C w ↔ Reach n C j w := by
  unfold A
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(reach_and n C hC j w h).2.1, h⟩

lemma A_and (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (h1 : n ≤ w)
    (h2 : w < n + C.gates.length) (hop : (gateAt C (w - n)).op = GateOp.and) :
    A n C w = {w} := by
  ext j
  rw [mem_A n C hC, Finset.mem_singleton]
  constructor
  · intro h
    rcases reach_inv n C j w h with ⟨h0, _⟩ | ⟨_, _, h3, _⟩
    · exact h0
    · rw [hop] at h3; exact absurd h3 (by simp)
  · rintro rfl
    exact Reach.self j h1 h2 hop

lemma z_cls (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (hz : Z n C w) :
    (A n C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Z n C a ∧ Z n C b ∧ A n C w = A n C a ∪ A n C b := by
  rcases z_struct n C hC w hz with hop | ⟨hop, a, b, hab, ha, hb, za, zb, _⟩
  · left; rw [A_and n C hC w hz.1 hz.2.1 hop]; simp
  · right
    refine ⟨a, b, ha, hb, za, zb, ?_⟩
    ext j
    rw [Finset.mem_union, mem_A n C hC, mem_A n C hC, mem_A n C hC]
    constructor
    · intro h
      rcases reach_inv n C j w h with ⟨_, _, _, h3⟩ | ⟨_, _, _, a0, h4, h5⟩
      · rw [hop] at h3; exact absurd h3 (by simp)
      · rw [hab] at h4
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
        rcases h4 with rfl | rfl
        · exact Or.inl h5
        · exact Or.inr h5
    · rintro (h | h)
      · exact Reach.up j w a hz.1 hz.2.1 hop (by rw [hab]; simp) h
      · exact Reach.up j w b hz.1 hz.2.1 hop (by rw [hab]; simp) h


-- the class of wires in P or L: inputs, or OR gates of two wires of the class
def QH (Q : ℕ → Prop) : Prop := ∀ w, Q w → w < n ∨ ∃ k < C.gates.length, w = n + k ∧
  (gateAt C k).op = GateOp.or ∧ ∀ i ∈ (gateAt C k).inputs, Q i

lemma q_struct (hC : PEqualNP.TopForm.IsAO2 n C) (Q : ℕ → Prop) (hQ : QH n C Q) (w : ℕ)
    (hw : Q w) (hn : n ≤ w) :
    ∃ a b, a < w ∧ b < w ∧ Q a ∧ Q b ∧ w < n + C.gates.length ∧
      (gateAt C (w - n)).op = GateOp.or ∧
      ∀ x : Fin n → Bool, val C.gates x w = (val C.gates x a || val C.gates x b) := by
  rcases hQ w hw with h | ⟨k, hk, rfl, hop, hin⟩
  · omega
  obtain ⟨a, b, hab, ha, hb, _, hv⟩ := gv n C hC (n + k) hn (by omega)
  have e : n + k - n = k := by omega
  rw [e] at hab hv
  rw [e]
  refine ⟨a, b, ha, hb, hin a (by rw [hab]; simp), hin b (by rw [hab]; simp), by omega, hop,
    fun x => ?_⟩
  rw [hv x, hop, ev_or]

lemma q_sem (hC : PEqualNP.TopForm.IsAO2 n C) (Q : ℕ → Prop) (hQ : QH n C Q) :
    ∀ w, Q w → ∀ u v : Fin n,
    (val C.gates (pr u v) w = true ↔ (u ∈ S n C w ∨ v ∈ S n C w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw u v
    by_cases hn : w < n
    · rw [S_inp n C w hn, val_lt C.gates _ w hn]
      simp only [pr, decide_eq_true_eq, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
    · obtain ⟨a, b, ha, hb, la, lb, _, _, hv⟩ := q_struct n C hC Q hQ w hw (by omega)
      rw [hv, Bool.or_eq_true, ih a ha la, ih b hb lb, S_or n C a b w hv]
      simp only [Finset.mem_union]
      tauto

lemma q_ne (hC : PEqualNP.TopForm.IsAO2 n C) (Q : ℕ → Prop) (hQ : QH n C Q) :
    ∀ w, Q w → (S n C w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [S_inp n C w hn]; simp
    · obtain ⟨a, b, ha, hb, la, lb, _, _, hv⟩ := q_struct n C hC Q hQ w hw (by omega)
      rw [S_or n C a b w hv]
      obtain ⟨y, hy⟩ := ih a ha la
      exact ⟨y, Finset.mem_union_left _ hy⟩

lemma q_cls (hC : PEqualNP.TopForm.IsAO2 n C) (Q : ℕ → Prop) (hQ : QH n C Q) (w : ℕ) (hw : Q w) :
    (S n C w).card ≤ 1 ∨ ∃ a b, a < w ∧ b < w ∧ Q a ∧ Q b ∧ S n C w = S n C a ∪ S n C b := by
  by_cases hn : w < n
  · left; rw [S_inp n C w hn]; simp
  · obtain ⟨a, b, ha, hb, la, lb, _, _, hv⟩ := q_struct n C hC Q hQ w hw (by omega)
    exact Or.inr ⟨a, b, ha, hb, la, lb, S_or n C a b w hv⟩

lemma q_gate (hC : PEqualNP.TopForm.IsAO2 n C) (Q : ℕ → Prop) (hQ : QH n C Q) (k : ℕ) (hk : Q k)
    (h2 : 2 ≤ (S n C k).card) :
    n ≤ k ∧ k < n + C.gates.length ∧ (gateAt C (k - n)).op = GateOp.or := by
  have hn : n ≤ k := by
    by_contra h
    push_neg at h
    rw [S_inp n C k h, Finset.card_singleton] at h2
    omega
  obtain ⟨_, _, _, _, _, _, hlt, hor, _⟩ := q_struct n C hC Q hQ k hk hn
  exact ⟨hn, hlt, hor⟩

end circ

def AH (C : Circuit) (Q : ℕ → Prop) : Prop := ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
  ∃ a b, (gateAt C k).inputs = [a, b] ∧ Q a ∧ Q b

def Good (n : ℕ) (C : Circuit) (Q : ℕ → Prop) (adj : Fin n → Fin n → Prop) : Prop :=
  PEqualNP.TopForm.IsAO2 n C ∧ QH n C Q ∧ AH C Q ∧ (∀ v, ¬ adj v v) ∧
  (∀ u v, adj u v → adj v u) ∧
  (∀ c c' y y' : Fin n, c ≠ c' → y ≠ y' → adj c y → adj c y' → adj c' y → adj c' y' → False) ∧
  (∀ u v : Fin n, val C.gates (pr u v) C.output = true ↔ adj u v)

section stars

variable (n : ℕ) (C : Circuit) (Q : ℕ → Prop) (adj : Fin n → Fin n → Prop)

lemma pr_self (v : Fin n) : pr v v = eof v := by
  funext c; simp [pr, eof]

lemma out_Z (hG : Good n C Q adj) (hex : ∃ u v, adj u v) : Z n C C.output := by
  obtain ⟨_, _, _, hirr, _, _, hout⟩ := hG
  have hf : ∀ v : Fin n, val C.gates (eof v) C.output = false := by
    intro v
    rw [← pr_self]
    cases hv : val C.gates (pr v v) C.output
    · rfl
    · rw [hout] at hv; exact absurd hv (hirr v)
  refine ⟨?_, ?_, hf⟩
  · by_contra h
    push_neg at h
    have := hf ⟨C.output, h⟩
    rw [val_lt C.gates _ _ h] at this
    simp [eof] at this
  · by_contra h
    push_neg at h
    obtain ⟨u, v, huv⟩ := hex
    have h1 := (hout u v).mpr huv
    rw [val_ge C.gates _ _ h] at h1
    exact absurd h1 (by simp)

def ia (j : ℕ) : ℕ := (gateAt C (j - n)).inputs.getD 0 0

def ib (j : ℕ) : ℕ := (gateAt C (j - n)).inputs.getD 1 0

lemma star (hG : Good n C Q adj) (j : ℕ) (hj : Reach n C j C.output) :
    Q (ia n C j) ∧ Q (ib n C j) ∧ ia n C j < j ∧ ib n C j < j ∧
      ∀ u v : Fin n, (val C.gates (pr u v) j = true ↔
        (u ∈ S n C (ia n C j) ∨ v ∈ S n C (ia n C j)) ∧
          (u ∈ S n C (ib n C j) ∨ v ∈ S n C (ib n C j))) := by
  obtain ⟨hC, hQ, hA, _, _, _, _⟩ := hG
  obtain ⟨h1, h2, hop, _⟩ := reach_and n C hC j _ hj
  obtain ⟨a, b, hab, ha, hb, _, hv⟩ := gv n C hC j h1 h2
  obtain ⟨a', b', hab', qa, qb⟩ := hA (j - n) (by omega) hop
  rw [hab] at hab'
  simp only [List.cons.injEq, and_true] at hab'
  rw [← hab'.1] at qa
  rw [← hab'.2] at qb
  have ea : ia n C j = a := by simp [ia, hab]
  have eb : ib n C j = b := by simp [ib, hab]
  rw [ea, eb]
  refine ⟨qa, qb, ha, hb, fun u v => ?_⟩
  rw [hv, hop, ev_and, Bool.and_eq_true, q_sem n C hC Q hQ a qa, q_sem n C hC Q hQ b qb]

lemma star2 (hG : Good n C Q adj) (j : ℕ) (hj : Reach n C j C.output) :
    (∀ v, ¬ (v ∈ S n C (ia n C j) ∧ v ∈ S n C (ib n C j))) ∧
    (∀ u ∈ S n C (ia n C j), ∀ v ∈ S n C (ib n C j), adj u v) ∧
    ((S n C (ia n C j)).card = 1 ∨ (S n C (ib n C j)).card = 1) := by
  obtain ⟨la, lb, _, _, hs⟩ := star n C Q adj hG j hj
  obtain ⟨hC, hQ, _, hirr, _, hcom, hout⟩ := hG
  have hadj : ∀ u v, val C.gates (pr u v) j = true → adj u v := by
    intro u v h
    exact (hout u v).mp (reach_val n C hC j _ hj _ h)
  have hd : ∀ v, ¬ (v ∈ S n C (ia n C j) ∧ v ∈ S n C (ib n C j)) := by
    rintro v ⟨h1, h2⟩
    exact hirr v (hadj v v ((hs v v).mpr ⟨Or.inl h1, Or.inl h2⟩))
  have hc : ∀ u ∈ S n C (ia n C j), ∀ v ∈ S n C (ib n C j), adj u v :=
    fun u hu v hv => hadj u v ((hs u v).mpr ⟨Or.inl hu, Or.inr hv⟩)
  refine ⟨hd, hc, ?_⟩
  by_contra hne
  push_neg at hne
  have n1 := (q_ne n C hC Q hQ _ la).card_pos
  have n2 := (q_ne n C hC Q hQ _ lb).card_pos
  obtain ⟨p1, hp1, p2, hp2, hp⟩ :=
    Finset.one_lt_card.mp (show 1 < (S n C (ia n C j)).card by omega)
  obtain ⟨q1, hq1, q2, hq2, hq⟩ :=
    Finset.one_lt_card.mp (show 1 < (S n C (ib n C j)).card by omega)
  exact hcom p1 p2 q1 q2 hp hq (hc p1 hp1 q1 hq1) (hc p1 hp1 q2 hq2) (hc p2 hp2 q1 hq1)
    (hc p2 hp2 q2 hq2)

def cw (j : ℕ) : ℕ := if (S n C (ia n C j)).card = 1 then ia n C j else ib n C j

def lw (j : ℕ) : ℕ := if (S n C (ia n C j)).card = 1 then ib n C j else ia n C j

lemma cw_facts (hG : Good n C Q adj) (j : ℕ) (hj : Reach n C j C.output) :
    (S n C (cw n C j)).card = 1 ∧ Q (lw n C j) ∧ lw n C j < j ∧
      (∀ c ∈ S n C (cw n C j), ∀ y ∈ S n C (lw n C j), adj c y) := by
  obtain ⟨la, lb, ha, hb, _⟩ := star n C Q adj hG j hj
  obtain ⟨_, hc, h1⟩ := star2 n C Q adj hG j hj
  have hsymm := hG.2.2.2.2.1
  by_cases h : (S n C (ia n C j)).card = 1
  · simp only [cw, lw, if_pos h]
    exact ⟨h, lb, hb, hc⟩
  · simp only [cw, lw, if_neg h]
    refine ⟨h1.resolve_left h, la, ha, fun c hc' y hy => ?_⟩
    exact hsymm _ _ (hc y hy c hc')

lemma cover (hG : Good n C Q adj) (u v : Fin n) (huv : adj u v) :
    ∃ j, Reach n C j C.output ∧ ((u ∈ S n C (cw n C j) ∧ v ∈ S n C (lw n C j)) ∨
      (v ∈ S n C (cw n C j) ∧ u ∈ S n C (lw n C j))) := by
  have hC := hG.1
  have hout := hG.2.2.2.2.2.2
  obtain ⟨j, hj, hv⟩ := z_sem n C hC _ (out_Z n C Q adj hG ⟨u, v, huv⟩) _ ((hout u v).mpr huv)
  refine ⟨j, hj, ?_⟩
  obtain ⟨_, _, _, _, hs⟩ := star n C Q adj hG j hj
  obtain ⟨hd, _, _⟩ := star2 n C Q adj hG j hj
  have h := (hs u v).mp hv
  have hu := hd u
  have hv' := hd v
  by_cases hc : (S n C (ia n C j)).card = 1
  · simp only [cw, lw, if_pos hc]
    tauto
  · simp only [cw, lw, if_neg hc]
    tauto

end stars

section count

variable (n : ℕ) (C : Circuit) (Q : ℕ → Prop) (adj : Fin n → Fin n → Prop)

lemma dbl (s : Finset ℕ) (T : ℕ → Finset (Fin n)) (h : ∀ j ∈ s, (T j).card = 1) :
    ∑ c : Fin n, (s.filter (fun j => c ∈ T j)).card = s.card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ j ∈ s, ∑ c : Fin n, (if c ∈ T j then 1 else 0) = 1 := by
    intro j hj
    rw [Finset.sum_boole]
    simp [Finset.filter_mem_eq_inter, h j hj]
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def G (c : Fin n) : Finset ℕ :=
  (A n C C.output).filter (fun j => c ∈ S n C (cw n C j))

noncomputable def D (c : Fin n) : Finset (Fin n) := (G n C c).biUnion (fun j => S n C (lw n C j))

noncomputable def Lc (c : Fin n) : Finset ℕ := (Finset.range (n + C.gates.length)).filter
  (fun k => Q k ∧ 2 ≤ (S n C k).card ∧ S n C k ⊆ D n C c)

noncomputable def LL : Finset ℕ := (Finset.range (n + C.gates.length)).filter
  (fun k => Q k ∧ 2 ≤ (S n C k).card)

noncomputable def PU : Finset ℕ := (Finset.range (n + C.gates.length)).filter
  (fun k => Z n C k ∧ 2 ≤ (A n C k).card ∧ A n C k ⊆ A n C C.output)

lemma memG (c : Fin n) (j : ℕ) : j ∈ G n C c ↔ j ∈ A n C C.output ∧ c ∈ S n C (cw n C j) := by
  simp [G]

lemma memD (c y : Fin n) : y ∈ D n C c ↔ ∃ j ∈ G n C c, y ∈ S n C (lw n C j) := by
  simp [D]

lemma dn (hG : Good n C Q adj) (c : Fin n) : ∀ y ∈ D n C c, adj c y := by
  intro y hy
  obtain ⟨j, hjG, hy⟩ := (memD n C c y).mp hy
  obtain ⟨hjA, hc⟩ := (memG n C c j).mp hjG
  exact (cw_facts n C Q adj hG j ((mem_A n C hG.1 j _).mp hjA)).2.2.2 c hc y hy

lemma dc_le (hG : Good n C Q adj) (c : Fin n) :
    (D n C c).card ≤ (G n C c).card + (Lc n C Q c).card := by
  have hC := hG.1
  have hW : ∀ w ∈ (G n C c).image (lw n C), w < n + C.gates.length ∧ Q w := by
    intro w hw
    obtain ⟨j, hjG, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hjA, _⟩ := (memG n C c j).mp hjG
    have hr := (mem_A n C hC j _).mp hjA
    obtain ⟨_, hl, hlt, _⟩ := cw_facts n C Q adj hG j hr
    have := (reach_and n C hC j _ hr).2.1
    exact ⟨by omega, hl⟩
  have h := leaf_count Q (S n C) (q_cls n C hC Q hG.2.1) _ _ hW
  rw [Finset.image_biUnion] at h
  have hi : ((G n C c).image (lw n C)).card ≤ (G n C c).card := Finset.card_image_le
  have h' : (D n C c).card ≤ ((G n C c).image (lw n C)).card + (Lc n C Q c).card := h
  omega

lemma lsum (hG : Good n C Q adj) : ∑ c : Fin n, (Lc n C Q c).card ≤ (LL n C Q).card := by
  have hcom := hG.2.2.2.2.2.1
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (Lc n C Q) := by
    intro c _ c' _ hne
    show Disjoint (Lc n C Q c) (Lc n C Q c')
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Lc, Finset.mem_filter] at hk hk'
    obtain ⟨y1, hy1, y2, hy2, hy⟩ := Finset.one_lt_card.mp (show 1 < (S n C k).card by omega)
    have a1 := dn n C Q adj hG c y1 (hk.2.2.2 hy1)
    have a2 := dn n C Q adj hG c y2 (hk.2.2.2 hy2)
    have b1 := dn n C Q adj hG c' y1 (hk'.2.2.2 hy1)
    have b2 := dn n C Q adj hG c' y2 (hk'.2.2.2 hy2)
    exact hcom c c' y1 y2 hne hy a1 a2 b1 b2
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_biUnion] at hk
  obtain ⟨c, _, hk⟩ := hk
  simp only [Lc, LL, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.1, hk.2.2.1⟩

lemma gsum (hG : Good n C Q adj) : ∑ c : Fin n, (G n C c).card = (A n C C.output).card :=
  dbl n (A n C C.output) (fun j => S n C (cw n C j))
    (fun j hj => (cw_facts n C Q adj hG j ((mem_A n C hG.1 j _).mp hj)).1)

lemma cov (hG : Good n C Q adj) (u v : Fin n) (huv : adj u v) :
    ((G n C u).Nonempty ∧ v ∈ D n C u) ∨ ((G n C v).Nonempty ∧ u ∈ D n C v) := by
  obtain ⟨j, hj, h⟩ := cover n C Q adj hG u v huv
  have hjA : j ∈ A n C C.output := (mem_A n C hG.1 j _).mpr hj
  rcases h with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact Or.inl ⟨⟨j, (memG n C _ _).mpr ⟨hjA, hu⟩⟩,
      (memD n C _ _).mpr ⟨j, (memG n C _ _).mpr ⟨hjA, hu⟩, hv⟩⟩
  · exact Or.inr ⟨⟨j, (memG n C _ _).mpr ⟨hjA, hv⟩⟩,
      (memD n C _ _).mpr ⟨j, (memG n C _ _).mpr ⟨hjA, hv⟩, hu⟩⟩

lemma kcard (hG : Good n C Q adj) :
    (Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty)).card ≤ (A n C C.output).card := by
  rw [← gsum n C Q adj hG, Finset.card_eq_sum_ones]
  calc ∑ c ∈ Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty), 1
      ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty), (G n C c).card :=
        Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2.card_pos)
    _ ≤ ∑ c : Fin n, (G n C c).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma pu_le (hG : Good n C Q adj) (hex : ∃ u v, adj u v) :
    (A n C C.output).card ≤ 1 + (PU n C).card := by
  have hz := out_Z n C Q adj hG hex
  have h := leaf_count (Z n C) (A n C) (z_cls n C hG.1) (n + C.gates.length) {C.output} (by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ⟨hz.2.1, hz⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at h
  exact h

lemma size_le (hG : Good n C Q adj) :
    (LL n C Q).card + (A n C C.output).card + (PU n C).card ≤ C.gates.length := by
  have hC := hG.1
  have hLL : ∀ k ∈ LL n C Q, n ≤ k ∧ k < n + C.gates.length ∧
      (gateAt C (k - n)).op = GateOp.or := by
    intro k hk
    simp only [LL, Finset.mem_filter] at hk
    exact q_gate n C hC Q hG.2.1 k hk.2.1 hk.2.2
  have hAA : ∀ k ∈ A n C C.output, n ≤ k ∧ k < n + C.gates.length ∧
      (gateAt C (k - n)).op = GateOp.and := by
    intro k hk
    obtain ⟨h1, h2, h3, _⟩ := reach_and n C hC k _ ((mem_A n C hC k _).mp hk)
    exact ⟨h1, h2, h3⟩
  have hPP : ∀ k ∈ PU n C, Z n C k ∧ 2 ≤ (A n C k).card := by
    intro k hk
    simp only [PU, Finset.mem_filter] at hk
    exact ⟨hk.2.1, hk.2.2.1⟩
  have d1 : Disjoint (LL n C Q) (A n C C.output) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have := (hLL k h1).2.2
    rw [(hAA k h2).2.2] at this
    exact absurd this (by simp)
  have d2 : Disjoint (LL n C Q ∪ A n C C.output) (PU n C) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    obtain ⟨hz, h2c⟩ := hPP k h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · simp only [LL, Finset.mem_filter] at h1
      have : S n C k = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        rw [mem_S, hz.2.2 v] at hv
        exact absurd hv (by simp)
      rw [this] at h1
      simp at h1
    · obtain ⟨a1, a2, a3⟩ := hAA k h1
      rw [A_and n C hC k a1 a2 a3, Finset.card_singleton] at h2c
      omega
  have hsub : LL n C Q ∪ A n C C.output ∪ PU n C ⊆ Finset.Ico n (n + C.gates.length) := by
    intro k hk
    rw [Finset.mem_Ico]
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact ⟨(hLL k hk).1, (hLL k hk).2.1⟩
      · exact ⟨(hAA k hk).1, (hAA k hk).2.1⟩
    · exact ⟨(hPP k hk).1.1, (hPP k hk).1.2.1⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, Nat.card_Ico] at this
  omega

theorem core (hG : Good n C Q adj) (hex : ∃ u v, adj u v) :
    ∃ (K : Finset (Fin n)) (Dm : Fin n → Finset (Fin n)), (∀ u v, adj u v → u ∈ K ∨ v ∈ K) ∧
      (∀ u v, adj u v → v ∈ Dm u ∨ u ∈ Dm v) ∧
      (∑ c, (Dm c).card) + K.card ≤ C.gates.length + 1 := by
  refine ⟨Finset.univ.filter (fun c : Fin n => (G n C c).Nonempty), D n C, ?_, ?_, ?_⟩
  · intro u v huv
    rcases cov n C Q adj hG u v huv with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩)
  · intro u v huv
    rcases cov n C Q adj hG u v huv with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  · have e2 : ∑ c : Fin n, (D n C c).card ≤ (A n C C.output).card + (LL n C Q).card := by
      calc ∑ c : Fin n, (D n C c).card ≤ ∑ c : Fin n, ((G n C c).card + (Lc n C Q c).card) :=
            Finset.sum_le_sum (fun c _ => dc_le n C Q adj hG c)
        _ = ∑ c : Fin n, (G n C c).card + ∑ c : Fin n, (Lc n C Q c).card := Finset.sum_add_distrib
        _ ≤ (A n C C.output).card + (LL n C Q).card := by
            rw [gsum n C Q adj hG]
            exact Nat.add_le_add_left (lsum n C Q adj hG) _
    have e3 := kcard n C Q adj hG
    have e4 := pu_le n C Q adj hG hex
    have e5 := size_le n C Q adj hG
    omega

end count

end cl

-- the incidence structure as a symmetric adjacency on the n1 + n2 variables
lemma ca_ne_na {x1 x2 : ℕ} (p : Fin x1) (l : Fin x2) : Fin.castAdd x2 p ≠ Fin.natAdd x1 l := by
  intro h
  have h1 : p.val = x1 + l.val := congrArg Fin.val h
  have := p.isLt
  omega

lemma ca_inj {x1 x2 : ℕ} {p p' : Fin x1} (h : Fin.castAdd x2 p = Fin.castAdd x2 p') : p = p' := by
  have h1 := congrArg Fin.val h
  exact Fin.ext h1

lemma na_inj {x1 x2 : ℕ} {l l' : Fin x2} (h : Fin.natAdd x1 l = Fin.natAdd x1 l') : l = l' := by
  have h1 : x1 + l.val = x1 + l'.val := congrArg Fin.val h
  exact Fin.ext (by omega)

def adjI {x1 x2 : ℕ} (I : Fin x1 → Fin x2 → Prop) (u v : Fin (x1 + x2)) : Prop :=
  ∃ p l, I p l ∧ ((u = Fin.castAdd x2 p ∧ v = Fin.natAdd x1 l) ∨
    (u = Fin.natAdd x1 l ∧ v = Fin.castAdd x2 p))

lemma good_of (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) (C : Circuit) (P L : Finset ℕ)
    (hno : ∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 →
      ¬(I x8 x10 ∧ I x8 x11 ∧ I x9 x10 ∧ I x9 x11))
    (hC : PEqualNP.TopForm.IsAO2 (x1 + x2) C)
    (hF : ∀ x : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) C x = true ↔
      ∃ p l, I p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true)
    (hP : ∀ x11 ∈ P, x11 < x1 ∨ ∃ x13 < C.gates.length, x11 = x1 + x2 + x13 ∧
      (gateAt C x13).op = GateOp.or ∧ ∀ x14 ∈ (gateAt C x13).inputs, x14 ∈ P)
    (hL : ∀ x12 ∈ L, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < C.gates.length, x12 = x1 + x2 + x14 ∧
      (gateAt C x14).op = GateOp.or ∧ ∀ x15 ∈ (gateAt C x14).inputs, x15 ∈ L)
    (hAnd : ∀ x13 < C.gates.length, (gateAt C x13).op = GateOp.and →
      ∃ (x16 : ℕ) (x17 : ℕ), (gateAt C x13).inputs = [x16, x17] ∧ x16 ∈ L ∧ x17 ∈ P) :
    Good (x1 + x2) C (fun w => w ∈ P ∨ w ∈ L) (adjI I) := by
  refine ⟨hC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases hw with hw | hw
    · rcases hP w hw with h | ⟨k, hk, rfl, hop, hin⟩
      · left; omega
      · right; exact ⟨k, hk, rfl, hop, fun i hi => Or.inl (hin i hi)⟩
    · rcases hL w hw with h | ⟨k, hk, rfl, hop, hin⟩
      · left; omega
      · right; exact ⟨k, hk, rfl, hop, fun i hi => Or.inr (hin i hi)⟩
  · intro k hk hop
    obtain ⟨a, b, hab, ha, hb⟩ := hAnd k hk hop
    exact ⟨a, b, hab, Or.inr ha, Or.inl hb⟩
  · intro v hv
    unfold adjI at hv
    obtain ⟨p, l, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hv
    · exact ca_ne_na p l (h1.symm.trans h2)
    · exact ca_ne_na p l (h2.symm.trans h1)
  · intro u v h
    unfold adjI at h ⊢
    obtain ⟨p, l, i, h | h⟩ := h
    · exact ⟨p, l, i, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨p, l, i, Or.inl ⟨h.2, h.1⟩⟩
  · intro c c' y y' hc hy h1 h2 h3 h4
    unfold adjI at h1 h2 h3 h4
    obtain ⟨p1, l1, i1, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h1
    · obtain ⟨p2, l2, i2, ⟨e1, rfl⟩ | ⟨e1, _⟩⟩ := h2
      · obtain ⟨p3, l3, i3, ⟨rfl, e3⟩ | ⟨_, e3⟩⟩ := h3
        · obtain ⟨p4, l4, i4, ⟨e4, e5⟩ | ⟨e4, _⟩⟩ := h4
          · rw [← ca_inj e1] at i2
            rw [← na_inj e3] at i3
            rw [← ca_inj e4, ← na_inj e5] at i4
            exact hno p1 p3 l1 l2 (fun h => hc (by rw [h])) (fun h => hy (by rw [h]))
              ⟨i1, i2, i3, i4⟩
          · exact ca_ne_na _ _ e4
        · exact ca_ne_na _ _ e3.symm
      · exact ca_ne_na _ _ e1
    · obtain ⟨p2, l2, i2, ⟨e1, _⟩ | ⟨e1, rfl⟩⟩ := h2
      · exact ca_ne_na _ _ e1.symm
      · obtain ⟨p3, l3, i3, ⟨_, e3⟩ | ⟨rfl, e3⟩⟩ := h3
        · exact ca_ne_na _ _ e3
        · obtain ⟨p4, l4, i4, ⟨e4, _⟩ | ⟨e4, e5⟩⟩ := h4
          · exact ca_ne_na _ _ e4.symm
          · rw [← na_inj e1] at i2
            rw [← ca_inj e3] at i3
            rw [← na_inj e4, ← ca_inj e5] at i4
            exact hno p1 p2 l1 l3 (fun h => hy (by rw [h])) (fun h => hc (by rw [h]))
              ⟨i1, i3, i2, i4⟩
  · intro u v
    have e : val C.gates (pr u v) C.output = circuitFun (x1 + x2) C (pr u v) := rfl
    rw [e, hF]
    simp only [pr, decide_eq_true_eq, adjI]
    constructor
    · rintro ⟨p, l, i, h1, h2⟩
      refine ⟨p, l, i, ?_⟩
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.trans h2.symm) (ca_ne_na p l)
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
      · exact absurd (h1.trans h2.symm) (ca_ne_na p l)
    · rintro ⟨p, l, i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨p, l, i, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨p, l, i, Or.inr rfl, Or.inl rfl⟩

lemma inj_count {x1 x2 : ℕ} (I : Fin x1 → Fin x2 → Prop)
    (Dm : Fin (x1 + x2) → Finset (Fin (x1 + x2)))
    (hD : ∀ p l, I p l →
      Fin.natAdd x1 l ∈ Dm (Fin.castAdd x2 p) ∨ Fin.castAdd x2 p ∈ Dm (Fin.natAdd x1 l)) :
    (PEqualNP.ReadTwo.incid I).card ≤ ∑ c, (Dm c).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun e => if Fin.natAdd x1 e.2 ∈ Dm (Fin.castAdd x2 e.1) then
      (⟨Fin.castAdd x2 e.1, Fin.natAdd x1 e.2⟩ : Σ _ : Fin (x1 + x2), Fin (x1 + x2))
      else ⟨Fin.natAdd x1 e.2, Fin.castAdd x2 e.1⟩) ?_ ?_
  · intro e he
    have he' : I e.1 e.2 := by simpa [PEqualNP.ReadTwo.incid] using he
    by_cases h : Fin.natAdd x1 e.2 ∈ Dm (Fin.castAdd x2 e.1)
    · simp [h]
    · rcases hD _ _ he' with h' | h'
      · exact absurd h' h
      · simp [h, h']
  · intro e _ e' _ hee
    dsimp only at hee
    by_cases h1 : Fin.natAdd x1 e.2 ∈ Dm (Fin.castAdd x2 e.1) <;>
      by_cases h2 : Fin.natAdd x1 e'.2 ∈ Dm (Fin.castAdd x2 e'.1)
    · rw [if_pos h1, if_pos h2] at hee
      obtain ⟨a, b⟩ := Sigma.mk.inj_iff.mp hee
      exact Prod.ext (ca_inj a) (na_inj (eq_of_heq b))
    · rw [if_pos h1, if_neg h2] at hee
      exact absurd (Sigma.mk.inj_iff.mp hee).1 (ca_ne_na _ _)
    · rw [if_neg h1, if_pos h2] at hee
      exact absurd (Sigma.mk.inj_iff.mp hee).1.symm (ca_ne_na _ _)
    · rw [if_neg h1, if_neg h2] at hee
      obtain ⟨a, b⟩ := Sigma.mk.inj_iff.mp hee
      exact Prod.ext (ca_inj (eq_of_heq b)) (na_inj a)

theorem main (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I] (C : Circuit)
    (P L : Finset ℕ)
    (hno : ∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 →
      ¬(I x8 x10 ∧ I x8 x11 ∧ I x9 x10 ∧ I x9 x11))
    (hC : PEqualNP.TopForm.IsAO2 (x1 + x2) C)
    (hF : ∀ (x10 : Fin (x1 + x2) → Bool), circuitFun (x1 + x2) C x10 =
      Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), I x11 x12 ∧
        x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true))
    (hP : ∀ x11 ∈ P, x11 < x1 ∨ ∃ x13 < C.gates.length, x11 = x1 + x2 + x13 ∧
      (gateAt C x13).op = GateOp.or ∧ ∀ x14 ∈ (gateAt C x13).inputs, x14 ∈ P)
    (hL : ∀ x12 ∈ L, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < C.gates.length, x12 = x1 + x2 + x14 ∧
      (gateAt C x14).op = GateOp.or ∧ ∀ x15 ∈ (gateAt C x14).inputs, x15 ∈ L)
    (hAnd : ∀ x13 < C.gates.length, (gateAt C x13).op = GateOp.and →
      ∃ (x16 : ℕ) (x17 : ℕ), (gateAt C x13).inputs = [x16, x17] ∧ x16 ∈ L ∧ x17 ∈ P) :
    ∃ (K : Finset (Fin (x1 + x2))), (∀ (p : Fin x1) (l : Fin x2), I p l →
      Fin.castAdd x2 p ∈ K ∨ Fin.natAdd x1 l ∈ K) ∧
      (PEqualNP.ReadTwo.incid I).card + K.card ≤ C.size + (1 : ℕ) := by
  have hF' : ∀ x : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) C x = true ↔
      ∃ p l, I p l ∧ x (Fin.castAdd x2 p) = true ∧ x (Fin.natAdd x1 l) = true := by
    intro x
    rw [hF x, decide_eq_true_eq]
  have hG := good_of x1 x2 I C P L hno hC hF' hP hL hAnd
  have hadj : ∀ p l, I p l → adjI I (Fin.castAdd x2 p) (Fin.natAdd x1 l) := by
    intro p l h
    unfold adjI
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩
  by_cases hex : ∃ p l, I p l
  · obtain ⟨p0, l0, h0⟩ := hex
    obtain ⟨K, Dm, hK, hD, hcnt⟩ := core (x1 + x2) C _ _ hG ⟨_, _, hadj p0 l0 h0⟩
    refine ⟨K, fun p l h => hK _ _ (hadj p l h), ?_⟩
    have := inj_count I Dm (fun p l h => hD _ _ (hadj p l h))
    show _ ≤ C.gates.length + 1
    omega
  · refine ⟨∅, fun p l h => absurd ⟨p, l, h⟩ hex, ?_⟩
    have : PEqualNP.ReadTwo.incid I = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      simp only [PEqualNP.ReadTwo.incid, Finset.mem_filter] at he
      exact hex ⟨e.1, e.2, he.2⟩
    rw [this]
    simp

end PEqualNP.Outside.L_meta_4990_aux

theorem PEqualNP.Outside.L_meta_4990 : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Finset ℕ), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬(x3 x8 x10 ∧ x3 x8 x11 ∧ x3 x9 x10 ∧ x3 x9 x11)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → (∀ x11 ∈ x6, x11 < x1 ∨ ∃ x13 < x5.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs, x14 ∈ x6) → (∀ x12 ∈ x7, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x5.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).inputs, x15 ∈ x7) → (∀ x13 < x5.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x16 : ℕ) (x17 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs = [x16, x17] ∧ x16 ∈ x7 ∧ x17 ∈ x6) → ∃ (x14 : Finset (Fin (x1 + x2))), (∀ (x15 : Fin x1) (x16 : Fin x2), x3 x15 x16 → Fin.castAdd x2 x15 ∈ x14 ∨ Fin.natAdd x1 x16 ∈ x14) ∧ (PEqualNP.ReadTwo.incid x3).card + x14.card ≤ x5.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 x6 x7 h1 h2 h3 h4 h5 h6
  exact PEqualNP.Outside.L_meta_4990_aux.main x1 x2 x3 x5 x6 x7 h1 h2 h3 h4 h5 h6
