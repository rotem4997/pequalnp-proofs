import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1799
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

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

/-- The value of wire `w` on input `x`. -/
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem mono3 (gs : List Gate) (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := hao g (by simp)
    have := ih (fun g' hg' => hao g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

open PEqualNP.LowMerge in
theorem ri_len (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) :
    (restrictInput P L w pts).length = P + L := by
  simp [restrictInput]

open PEqualNP.LowMerge in
theorem ri_mono (P L : ℕ) (w : Fin L) (pts pts' : Fin P → Bool)
    (h : ∀ p, pts p = true → pts' p = true) (i : ℕ) :
    (restrictInput P L w pts).getD i false = true →
    (restrictInput P L w pts').getD i false = true := by
  unfold restrictInput
  by_cases hi : i < P
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
    exact h ⟨i, hi⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi),
      List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp

-- The value of a gate reading two earlier wires.
theorem pair_val (gates : List Gate) (X : List Bool) (j a b : ℕ) (op : GateOp)
    (hj : gates[j]? = some ⟨op, [a, b]⟩) (ha : a < X.length + j) (hb : b < X.length + j) :
    (wf gates X).getD (X.length + j) false
      = op.eval [(wf gates X).getD a false, (wf gates X).getD b false] := by
  have hlt : j < gates.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hj
    exact absurd hj (by simp)
  have hg : gates[j] = ⟨op, [a, b]⟩ := by
    rw [List.getElem?_eq_getElem hlt] at hj
    exact Option.some.inj hj
  rw [gate_val gates X j hlt, hg]
  simp only [List.map_cons, List.map_nil]
  rw [← wire_take gates X j a ha (Nat.le_of_lt hlt), ← wire_take gates X j b hb (Nat.le_of_lt hlt)]

open PEqualNP.LowMerge in
theorem and_low (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit)
    (hmono : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (j a b : ℕ)
    (hj : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < P + L + j) (hb : b < P + L + j)
    (w : Fin L) (hlow : IsLow P L inc C (P + L + j) w) :
    IsLow P L inc C a w ∨ IsLow P L inc C b w := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold IsLow at h1 h2
  push_neg at h1 h2
  obtain ⟨p1, ht1, hl1⟩ := h1
  obtain ⟨p2, ht2, hl2⟩ := h2
  let pts : Fin P → Bool := fun p => p1 p || p2 p
  have hup : ∀ (g : ℕ) (q : Fin P → Bool), (∀ p, q p = true → pts p = true) →
      wireVal C (restrictInput P L w q) g = true → wireVal C (restrictInput P L w pts) g = true :=
    fun g q hq h => mono3 C.gates hmono _ _ (by rw [ri_len, ri_len]) (ri_mono P L w q pts hq) g h
  have ta := hup a p1 (fun p hp => by simp [pts, hp]) ht1
  have tb := hup b p2 (fun p hp => by simp [pts, hp]) ht2
  have hg := pair_val C.gates (restrictInput P L w pts) j a b GateOp.and hj
    (by rw [ri_len]; exact ha) (by rw [ri_len]; exact hb)
  rw [ri_len] at hg
  have tg : wireVal C (restrictInput P L w pts) (P + L + j) = true := by
    show (wf C.gates (restrictInput P L w pts)).getD (P + L + j) false = true
    rw [hg]
    have ta' : (wf C.gates (restrictInput P L w pts)).getD a false = true := ta
    have tb' : (wf C.gates (restrictInput P L w pts)).getD b false = true := tb
    rw [ta', tb']
    rfl
  have hsum := hlow pts tg
  simp only [lineSum, decide_eq_true_eq] at hsum hl1 hl2
  obtain ⟨p, hp, hpp⟩ := hsum
  have hor : p1 p = true ∨ p2 p = true := by simpa [pts] using hpp
  rcases hor with h | h
  · exact hl1 (decide_eq_true ⟨p, hp, h⟩)
  · exact hl2 (decide_eq_true ⟨p, hp, h⟩)

end PEqualNP.Outside.L_meta_1799

open PEqualNP.Outside.L_meta_1799 PEqualNP.CircuitLowerBounds PEqualNP.LowMerge in
theorem PEqualNP.Outside.L_meta_1799 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ) (op : PEqualNP.CircuitLowerBounds.GateOp), (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or) → C.gates[j]? = some ⟨op, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ (w : Fin L) (y : Fin P), PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → y ∈ PEqualNP.LowMerge.aliveSet P L C (P + L + j) w → (PEqualNP.LowMerge.IsLow P L inc C a w ∧ y ∈ PEqualNP.LowMerge.aliveSet P L C a w) ∨ (PEqualNP.LowMerge.IsLow P L inc C b w ∧ y ∈ PEqualNP.LowMerge.aliveSet P L C b w) := by
  intro P L inc C hmono j a b op hop hj ha hb w y hlow hy
  have hval : ∀ X : List Bool, X.length = P + L →
      (wf C.gates X).getD (P + L + j) false
        = op.eval [(wf C.gates X).getD a false, (wf C.gates X).getD b false] := by
    intro X hX
    have := pair_val C.gates X j a b op hj (by rw [hX]; exact ha) (by rw [hX]; exact hb)
    rw [hX] at this
    exact this
  have hyt : (wf C.gates (pointLineInput P L y w)).getD (P + L + j) false = true := by
    have : wireVal C (pointLineInput P L y w) (P + L + j) = true := by
      simpa [aliveSet] using hy
    exact this
  rw [hval _ (by simp [pointLineInput, ri_len])] at hyt
  have mem : ∀ g : ℕ, (wf C.gates (pointLineInput P L y w)).getD g false = true →
      y ∈ aliveSet P L C g w := by
    intro g hg
    simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hg
  rcases hop with rfl | rfl
  · have hab : (wf C.gates (pointLineInput P L y w)).getD a false = true ∧
        (wf C.gates (pointLineInput P L y w)).getD b false = true := by
      simpa [GateOp.eval] using hyt
    rcases and_low P L inc C hmono j a b hj ha hb w hlow with h | h
    · exact Or.inl ⟨h, mem a hab.1⟩
    · exact Or.inr ⟨h, mem b hab.2⟩
  · have low : ∀ c : ℕ, (c = a ∨ c = b) → IsLow P L inc C c w := by
      intro c hc pts hpt
      apply hlow pts
      show (wf C.gates (restrictInput P L w pts)).getD (P + L + j) false = true
      rw [hval _ (ri_len P L w pts)]
      have hpt' : (wf C.gates (restrictInput P L w pts)).getD c false = true := hpt
      rcases hc with rfl | rfl
      · rw [hpt']; simp [GateOp.eval]
      · rw [hpt']; simp [GateOp.eval]
    have hab : (wf C.gates (pointLineInput P L y w)).getD a false = true ∨
        (wf C.gates (pointLineInput P L y w)).getD b false = true := by
      simpa [GateOp.eval] using hyt
    rcases hab with h | h
    · exact Or.inl ⟨low a (Or.inl rfl), mem a h⟩
    · exact Or.inr ⟨low b (Or.inr rfl), mem b h⟩
