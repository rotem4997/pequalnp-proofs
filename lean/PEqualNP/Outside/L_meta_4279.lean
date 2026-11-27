import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4279_aux

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

def rank (D : Finset ℕ) (j : ℕ) : ℕ := ((List.range j).filter (fun i => decide (i ∈ D))).length

lemma rank_succ (D : Finset ℕ) (j : ℕ) :
    rank D (j + 1) = rank D j + (if j ∈ D then 1 else 0) := by
  unfold rank
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : j ∈ D <;> simp [h]

lemma rank_mono (D : Finset ℕ) {a b : ℕ} (h : a ≤ b) : rank D a ≤ rank D b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [rank_succ]
    omega

lemma rank_lt (D : Finset ℕ) {a b : ℕ} (ha : a ∈ D) (h : a < b) : rank D a < rank D b := by
  have h1 := rank_succ D a
  rw [if_pos ha] at h1
  have h2 : rank D (a + 1) ≤ rank D b := rank_mono D h
  omega

lemma rank_le (D : Finset ℕ) (j : ℕ) : rank D j ≤ j := by
  unfold rank
  exact (List.length_filter_le _ _).trans (by simp)

def phi (n s : ℕ) (D : Finset ℕ) (w : ℕ) : ℕ :=
  if w < n then w else if w - n ∈ D then n + rank D (w - n) else n + s

def rho (n s : ℕ) (D : Finset ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi n s D)⟩

def B (n s : ℕ) (D : Finset ℕ) (C : Circuit) (m : ℕ) : List Gate :=
  ((List.range m).filter (fun i => decide (i ∈ D))).map (fun j => rho n s D (gateAt C j))

lemma B_length (n s : ℕ) (D : Finset ℕ) (C : Circuit) (m : ℕ) :
    (B n s D C m).length = rank D m := by
  simp [B, rank]

lemma B_succ (n s : ℕ) (D : Finset ℕ) (C : Circuit) (m : ℕ) :
    B n s D C (m + 1) = B n s D C m ++ (if m ∈ D then [rho n s D (gateAt C m)] else []) := by
  unfold B
  rw [List.range_succ, List.filter_append, List.map_append]
  by_cases h : m ∈ D <;> simp [h]

lemma liftA (n : ℕ) (C : Circuit) (D : Finset ℕ) (x : Fin n → Bool) (m : ℕ)
    (hm : m ≤ C.gates.length)
    (IH : ∀ j ∈ D, val (B n C.gates.length D C m) x (n + rank D j) = true →
      W n C x (n + j) = true ∧ j < m) :
    ∀ w, val (B n C.gates.length D C m) x (phi n C.gates.length D w) = true →
      W n C x w = true ∧ w < n + m := by
  intro w h
  by_cases hw : w < n
  · have hp : phi n C.gates.length D w = w := by simp [phi, hw]
    rw [hp, val_lt _ _ w hw] at h
    exact ⟨by rw [W_input n C x w hw]; exact h, by omega⟩
  · by_cases hd : w - n ∈ D
    · have hp : phi n C.gates.length D w = n + rank D (w - n) := by simp [phi, hw, hd]
      rw [hp] at h
      obtain ⟨h1, h2⟩ := IH (w - n) hd h
      have e : n + (w - n) = w := by omega
      rw [e] at h1
      exact ⟨h1, by omega⟩
    · have hp : phi n C.gates.length D w = n + C.gates.length := by simp [phi, hw, hd]
      rw [hp, val_ge _ _ _ (by rw [B_length]; have := rank_le D m; omega)] at h
      exact absurd h (by simp)

lemma invA (n : ℕ) (C : Circuit) (D : Finset ℕ) (x : Fin n → Bool)
    (hG : ∀ j ∈ D, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    ∀ m, m ≤ C.gates.length → ∀ j ∈ D,
      val (B n C.gates.length D C m) x (n + rank D j) = true →
      W n C x (n + j) = true ∧ j < m := by
  intro m
  induction m with
  | zero =>
    intro _ j _ h
    rw [val_ge _ _ _ (by rw [B_length]; simp [rank])] at h
    exact absurd h (by simp)
  | succ m ih =>
    intro hm j hjD h
    have ih' := ih (by omega)
    rw [B_succ] at h
    by_cases hmD : m ∈ D
    · rw [if_pos hmD, val_snoc, B_length] at h
      by_cases hj : j = m
      · subst hj
        rw [if_pos rfl] at h
        refine ⟨?_, by omega⟩
        rw [W_gate n C x j (by omega)]
        refine eval_mono _ (hG j hmD) (gateAt C j).inputs
          (fun w => val (B n C.gates.length D C j) x (phi n C.gates.length D w))
          (fun i => if i < n + j then W n C x i else false) ?_ ?_
        · intro w _ hw
          obtain ⟨h1, h2⟩ := liftA n C D x j (by omega) ih' w hw
          rw [if_pos h2]
          exact h1
        · simp only [rho, List.map_map] at h
          exact h
      · have hne : rank D j ≠ rank D m := by
          rcases lt_or_gt_of_ne hj with h' | h'
          · exact (rank_lt D hjD h').ne
          · exact (rank_lt D hmD h').ne'
        rw [if_neg (by omega)] at h
        obtain ⟨h1, h2⟩ := ih' j hjD h
        exact ⟨h1, by omega⟩
    · rw [if_neg hmD, List.append_nil] at h
      obtain ⟨h1, h2⟩ := ih' j hjD h
      exact ⟨h1, by omega⟩

lemma liftB (n : ℕ) (C : Circuit) (D : Finset ℕ) (x : Fin n → Bool) (m : ℕ)
    (hm : m ≤ C.gates.length)
    (hLD : ∀ j, j < C.gates.length → IsLive n C x (n + j) → j ∈ D)
    (IH : ∀ j, j < m → IsLive n C x (n + j) →
      val (B n C.gates.length D C m) x (n + rank D j) = true) :
    ∀ w, w < n + m → IsLive n C x w →
      val (B n C.gates.length D C m) x (phi n C.gates.length D w) = true := by
  intro w hwm hl
  by_cases hw : w < n
  · have hp : phi n C.gates.length D w = w := by simp [phi, hw]
    rw [hp, val_lt _ _ w hw, ← W_input n C x w hw]
    exact live_true n C x w hl
  · have e : n + (w - n) = w := by omega
    have hl' : IsLive n C x (n + (w - n)) := by rw [e]; exact hl
    have hd : w - n ∈ D := hLD (w - n) (by omega) hl'
    have hp : phi n C.gates.length D w = n + rank D (w - n) := by simp [phi, hw, hd]
    rw [hp]
    exact IH (w - n) (by omega) hl'

lemma invB (n : ℕ) (C : Circuit) (D : Finset ℕ) (x : Fin n → Bool)
    (hG : ∀ j ∈ D, (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or)
    (hLD : ∀ j, j < C.gates.length → IsLive n C x (n + j) → j ∈ D) :
    ∀ m, m ≤ C.gates.length → ∀ j, j < m → IsLive n C x (n + j) →
      val (B n C.gates.length D C m) x (n + rank D j) = true := by
  intro m
  induction m with
  | zero =>
    intro _ j hj _
    omega
  | succ m ih =>
    intro hm j hj hl
    have ih' := ih (by omega)
    rw [B_succ]
    by_cases hmD : m ∈ D
    · rw [if_pos hmD, val_snoc, B_length]
      by_cases hjm : j = m
      · subst hjm
        rw [if_pos rfl]
        have hW := live_true n C x (n + j) hl
        rw [W_gate n C x j (by omega)] at hW
        have key := eval_mono _ (hG j hmD) (gateAt C j).inputs
          (fun i => if i < n + j then W n C x i else false)
          (fun w => val (B n C.gates.length D C j) x (phi n C.gates.length D w)) ?_ hW
        · simp only [rho, List.map_map]
          exact key
        · intro w hwin hw
          by_cases hlt : w < n + j
          · rw [if_pos hlt] at hw
            exact liftB n C D x j (by omega) hLD ih' w hlt
              (live_back n C x j (by omega) hl w hwin hlt hw)
          · rw [if_neg hlt] at hw
            exact absurd hw (by simp)
      · have hjD : j ∈ D := hLD j (by omega) hl
        have hne : rank D j ≠ rank D m := (rank_lt D hjD (by omega)).ne
        rw [if_neg (by omega)]
        exact ih' j (by omega) hl
    · rw [if_neg hmD, List.append_nil]
      have hjm : j ≠ m := by
        intro e
        subst e
        exact hmD (hLD j (by omega) hl)
      exact ih' j (by omega) hl

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

lemma w7_le (n : ℕ) (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length)
    (x : Fin n → Bool) : ∀ w, W n (C7 C k) x w = true → W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h1 : w < n
    · rw [W_input n _ x w h1] at h
      rw [W_input n C x w h1]
      exact h
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [W_big n (C7 C k) x w (by rw [C7_len]; exact h2)] at h
        exact absurd h (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        by_cases hjk : j = k
        · subst hjk
          rw [W7_k n C j hj x] at h
          exact absurd h (by simp)
        · rw [W_gate n (C7 C k) x j (by rw [C7_len]; exact hj), C7_gate_ne C k j hjk] at h
          rw [W_gate n C x j hj]
          refine eval_mono _ (gate_ok C hM j hj).1 _ _ _ ?_ h
          intro a _ ha
          by_cases hlt : a < n + j
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)

theorem main (n : ℕ) (C : Circuit) (k : ℕ) (X : Finset (Fin n → Bool))
    (hM : Monotone2 C) (hk : k < C.size) (D : Finset ℕ)
    (hD : ∀ j, j ∈ D ↔ (j ∈ (Finset.range C.size).erase k ∧
      ∃ x ∈ X, IsLive n (C7 C k) x (n + j))) :
    ∃ C8 : Circuit, Monotone2 C8 ∧ circuitFun n C8 ≤ circuitFun n C ∧
      (∀ x ∈ X, circuitFun n C8 x = circuitFun n (C7 C k) x) ∧ C8.size ≤ D.card := by
  have hk' : k < C.gates.length := hk
  have hlen := C7_len C k
  have hDlt : ∀ j ∈ D, j < C.gates.length ∧ j ≠ k := by
    intro j hj
    have := ((hD j).mp hj).1
    simp only [Finset.mem_erase, Finset.mem_range, Circuit.size] at this
    exact ⟨this.2, this.1⟩
  have hG : ∀ j ∈ D, (gateAt (C7 C k) j).op = GateOp.and ∨ (gateAt (C7 C k) j).op = GateOp.or := by
    intro j hj
    rw [C7_gate_ne C k j (hDlt j hj).2]
    exact (gate_ok C hM j (hDlt j hj).1).1
  have hLD : ∀ x ∈ X, ∀ j, j < (C7 C k).gates.length → IsLive n (C7 C k) x (n + j) → j ∈ D := by
    intro x hx j hj hl
    rw [hlen] at hj
    refine (hD j).mpr ⟨?_, x, hx, hl⟩
    simp only [Finset.mem_erase, Finset.mem_range, Circuit.size]
    refine ⟨?_, hj⟩
    intro e
    rw [e] at hl
    have := live_true n (C7 C k) x (n + k) hl
    rw [W7_k n C k hk' x] at this
    exact absurd this (by simp)
  have hA : ∀ x : Fin n → Bool, ∀ w,
      val (B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length) x
        (phi n (C7 C k).gates.length D w) = true → W n (C7 C k) x w = true := by
    intro x w h
    exact (liftA n (C7 C k) D x _ le_rfl (invA n (C7 C k) D x hG _ le_rfl) w h).1
  refine ⟨⟨B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length,
    phi n (C7 C k).gates.length D C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [B, List.mem_map, List.mem_filter, List.mem_range] at hg
    obtain ⟨j, ⟨hj, _⟩, rfl⟩ := hg
    rw [hlen] at hj
    have hok : ((gateAt (C7 C k) j).op = GateOp.and ∨ (gateAt (C7 C k) j).op = GateOp.or) ∧
        (gateAt (C7 C k) j).inputs.length ≤ 2 := by
      by_cases hjk : j = k
      · subst hjk
        rw [C7_gate_k C j hj]
        simp
      · rw [C7_gate_ne C k j hjk]
        exact gate_ok C hM j hj
    refine ⟨?_, ?_⟩
    · have := hok.1
      simpa [rho] using this
    · simpa [rho] using hok.2
  · intro x
    refine Bool.le_iff_imp.mpr ?_
    intro h
    exact w7_le n C hM k hk' x C.output (hA x C.output h)
  · intro x hx
    have h1 : circuitFun n (C7 C k) x = true →
        val (B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length) x
          (phi n (C7 C k).gates.length D C.output) = true := by
      intro h
      have hW : W n (C7 C k) x (C7 C k).output = true := h
      have hl := live_out n (C7 C k) x hW
      have hlt : C.output < n + (C7 C k).gates.length := by
        by_contra hge
        have hf := W_big n (C7 C k) x C.output (by omega)
        have hW' : W n (C7 C k) x C.output = true := hW
        rw [hf] at hW'
        exact absurd hW' (by simp)
      exact liftB n (C7 C k) D x _ le_rfl (hLD x hx)
        (invB n (C7 C k) D x hG (hLD x hx) _ le_rfl) C.output hlt hl
    have h2 := hA x C.output
    show val (B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length) x
        (phi n (C7 C k).gates.length D C.output) = W n (C7 C k) x C.output
    have h1' : W n (C7 C k) x C.output = true →
        val (B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length) x
          (phi n (C7 C k).gates.length D C.output) = true := h1
    cases hv : val (B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length) x
        (phi n (C7 C k).gates.length D C.output) <;>
      cases hw : W n (C7 C k) x C.output
    · rfl
    · rw [h1' hw] at hv
      exact absurd hv (by simp)
    · rw [h2 hv] at hw
      exact absurd hw (by simp)
    · rfl
  · show (B n (C7 C k).gates.length D (C7 C k) (C7 C k).gates.length).length ≤ D.card
    rw [B_length, hlen]
    unfold rank
    have hnd : ((List.range C.gates.length).filter (fun i => decide (i ∈ D))).Nodup :=
      List.Nodup.filter _ List.nodup_range
    rw [← List.toFinset_card_of_nodup hnd]
    apply Finset.card_le_card
    intro j hj
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hj
    exact hj.2

end PEqualNP.Outside.L_meta_4279_aux

theorem PEqualNP.Outside.L_meta_4279 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Finset (Fin x1 → Bool)),   PEqualNP.MetaComplexity.Monotone2 x2 →     x3 < x2.size →       have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := PEqualNP.NotPremium.replaceByConst x2.gates x3 Bool.false, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit };       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ PEqualNP.MetaComplexity.circuitFun x1 x8 ≤ PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ x9 ∈ x4, PEqualNP.MetaComplexity.circuitFun x1 x8 x9 = PEqualNP.MetaComplexity.circuitFun x1 x7 x9) ∧ x8.size ≤ {x9 ∈ (Finset.range x2.size).erase x3 | ∃ x10 ∈ x4, PEqualNP.CarriedProduct.IsLive x1 x7 x10 (x1 + x9)}.card := by
  intro x1 x2 x3 x4 h1 h2
  exact PEqualNP.Outside.L_meta_4279_aux.main x1 x2 x3 x4 h1 h2 _ (fun j => Finset.mem_filter)
