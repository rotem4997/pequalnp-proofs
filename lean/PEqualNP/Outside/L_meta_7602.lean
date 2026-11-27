import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7602

-- live wire lemmas copied from the merged file L_meta_1603.lean
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CarriedProduct PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def F (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) : List ℕ :=
  ((List.range m).reverse).foldl (liveStep n C vals) L

lemma F_zero (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) :
    F n C vals 0 L = L := by
  simp [F]

lemma F_succ (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) :
    F n C vals (m + 1) L = F n C vals m (liveStep n C vals L m) := by
  simp [F, List.range_succ]

lemma step_sub (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ) (hw : w ∈ L) :
    w ∈ liveStep n C vals L j := by
  unfold liveStep
  split_ifs
  · exact List.mem_append_left _ hw
  · exact hw

lemma step_mem (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ)
    (h : w ∈ liveStep n C vals L j) :
    w ∈ L ∨ (n + j ∈ L ∧ w ∈ (gateAt C j).inputs ∧ w < n + j ∧ vals.getD w false = true) := by
  unfold liveStep at h
  split_ifs at h with hj
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inr ⟨hj, h.1, h.2.1, h.2.2⟩
  · exact Or.inl h

lemma F_sub (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ L → w ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero]; exact hw
  | succ m ih => intro L w hw; rw [F_succ]; exact ih _ w (step_sub n C vals L m w hw)

lemma F_mem (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ F n C vals m L → w ∈ L ∨ w < n + m := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero] at hw; exact Or.inl hw
  | succ m ih =>
    intro L w hw
    rw [F_succ] at hw
    rcases ih _ w hw with h | h
    · rcases step_mem n C vals L m w h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)

lemma F_true (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ), (∀ w ∈ L, vals.getD w false = true) →
      ∀ w ∈ F n C vals m L, vals.getD w false = true := by
  intro m
  induction m with
  | zero => intro L hL w hw; rw [F_zero] at hw; exact hL w hw
  | succ m ih =>
    intro L hL w hw
    rw [F_succ] at hw
    refine ih _ ?_ w hw
    intro w2 hw2
    rcases step_mem n C vals L m w2 hw2 with h | h
    · exact hL w2 h
    · exact h.2.2.2

lemma F_back (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (j : ℕ), j < m → n + j ∈ F n C vals m L →
      ∀ a ∈ (gateAt C j).inputs, a < n + j → vals.getD a false = true →
        a ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L j hj; omega
  | succ m ih =>
    intro L j hj hmem a ha hlt hv
    rw [F_succ] at hmem ⊢
    by_cases hjm : j < m
    · exact ih _ j hjm hmem a ha hlt hv
    · have hjeq : j = m := by omega
      subst hjeq
      have h1 : n + j ∈ liveStep n C vals L j := by
        rcases F_mem n C vals j _ _ hmem with h | h
        · exact h
        · omega
      have h2 : n + j ∈ L := by
        rcases step_mem n C vals L j _ h1 with h | h
        · exact h
        · exact h.1
      apply F_sub
      unfold liveStep
      rw [if_pos h2]
      refine List.mem_append_right _ ?_
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ha, hlt, hv⟩

lemma liveWires_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    liveWires n C x = F n C (C.wires (List.ofFn x)) C.gates.length
      (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else []) := rfl

lemma live_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : IsLive n C x w) :
    W n C x w = true := by
  unfold IsLive at h
  rw [liveWires_eq] at h
  refine F_true n C _ _ _ ?_ w h
  intro w2 hw2
  split_ifs at hw2 with hc
  · simp only [List.mem_singleton] at hw2
    rw [hw2]; exact hc
  · simp at hw2

lemma live_back (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (h : IsLive n C x (n + j)) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (hlt : a < n + j)
    (hv : W n C x a = true) : IsLive n C x a := by
  unfold IsLive at h ⊢
  rw [liveWires_eq] at h ⊢
  exact F_back n C _ _ _ j hj h a ha hlt hv

lemma live_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : W n C x C.output = true) :
    IsLive n C x C.output := by
  unfold IsLive
  rw [liveWires_eq]
  apply F_sub
  unfold W at h
  rw [if_pos h]
  simp


-- evaluation toolkit
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


lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ w ∈ l, f w = true → g w = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at h1 ⊢
    rintro b ⟨w, hw, rfl⟩
    exact h w hw (h1 _ ⟨w, hw, rfl⟩)
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at h1 ⊢
    obtain ⟨b, ⟨w, hw, rfl⟩, hb⟩ := h1
    exact ⟨_, ⟨w, hw, rfl⟩, h w hw hb⟩
def C7 (C : Circuit) (k : ℕ) : Circuit :=
  ⟨PEqualNP.NotPremium.replaceByConst C.gates k Bool.false, C.output⟩

lemma C7_len (C : Circuit) (k : ℕ) : (C7 C k).gates.length = C.gates.length := by
  simp [C7, PEqualNP.NotPremium.replaceByConst]

lemma C7_gate_k (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (C7 C k) k = ⟨GateOp.or, []⟩ := by
  simp [gateAt, C7, PEqualNP.NotPremium.replaceByConst, PEqualNP.NotPremium.constGate,
    List.getD_eq_getElem?_getD, hk]

lemma C7_gate_ne (C : Circuit) (k j : ℕ) (hj : j ≠ k) :
    gateAt (C7 C k) j = gateAt C j := by
  simp [gateAt, C7, PEqualNP.NotPremium.replaceByConst, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (Ne.symm hj)]

lemma gate_ok (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length ≤ 2 := by
  rw [gateAt_eq C j hj]
  obtain ⟨h1, h2⟩ := hM _ (List.getElem_mem hj)
  exact ⟨by simpa using h1, h2⟩

lemma W_big (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    W n C x w = false := by
  unfold W
  exact getD_ge_length _ _ (by rw [wires_length]; exact hw)

lemma W7_k (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    W n (C7 C k) x (n + k) = false := by
  rw [W_gate n (C7 C k) x k (by rw [C7_len]; exact hk), C7_gate_k C k hk]
  simp [GateOp.eval]


lemma w7_lt (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    ∀ w, w < n + k → W n (C7 C k) x w = W n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < n
    · rw [W_input n _ x w h1, W_input n C x w h1]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hjk : j ≠ k := by omega
      rw [W_gate n (C7 C k) x j (by rw [C7_len]; exact hj), C7_gate_ne C k j hjk,
        W_gate n C x j hj]
      congr 1
      refine List.map_congr_left fun a _ => ?_
      by_cases hlt : a < n + j
      · rw [if_pos hlt, if_pos hlt]
        exact ih a hlt (by omega)
      · rw [if_neg hlt, if_neg hlt]

lemma key (n : ℕ) (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length)
    (x : Fin n → Bool) :
    ∀ w, IsLive n C x w → W n (C7 C k) x w = false → IsLive n C x (n + k) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hl h7
    have ht := live_true n C x w hl
    by_cases hlt : w < n + k
    · rw [w7_lt n C k hk x w hlt, ht] at h7
      exact absurd h7 (by simp)
    by_cases heq : w = n + k
    · rw [heq] at hl; exact hl
    by_cases hbig : n + C.gates.length ≤ w
    · rw [W_big n C x w hbig] at ht
      exact absurd ht (by simp)
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hjk : j ≠ k := by omega
    rw [W_gate n (C7 C k) x j (by rw [C7_len]; exact hj), C7_gate_ne C k j hjk] at h7
    have ht' := ht
    rw [W_gate n C x j hj] at ht'
    by_contra hne
    have hall : ∀ a ∈ (gateAt C j).inputs,
        (if a < n + j then W n C x a else false) = true →
        (if a < n + j then W n (C7 C k) x a else false) = true := by
      intro a ha hfa
      by_cases hal : a < n + j
      · rw [if_pos hal] at hfa ⊢
        by_contra h7a
        have h7a' : W n (C7 C k) x a = false := by simpa using h7a
        exact hne (ih a hal (live_back n C x j hj hl a ha hal hfa) h7a')
      · rw [if_neg hal] at hfa
        exact absurd hfa (by simp)
    have := eval_mono _ (gate_ok C hM j hj).1 _ _ _ hall ht'
    rw [this] at h7
    exact absurd h7 (by simp)

end PEqualNP.Outside.L_meta_7602

theorem PEqualNP.Outside.L_meta_7602 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x2 → x3 < x2.size → ∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x6 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x2.gates x3 Bool.false, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit } x6 = Bool.false → PEqualNP.CarriedProduct.IsLive x1 x2 x6 (x1 + x3) := by
  intro n C k hM hk x h1 h2
  have hk' : k < C.gates.length := hk
  have hl : PEqualNP.CarriedProduct.IsLive n C x C.output :=
    PEqualNP.Outside.L_meta_7602.live_out n C x h1
  exact PEqualNP.Outside.L_meta_7602.key n C hM k hk' x C.output hl h2
