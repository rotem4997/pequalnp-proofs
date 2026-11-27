import Mathlib
import PEqualNP.Defs

/-!
# Every language has depth 3 circuits of exponential size

Helpers for `L031`: at length `n`, a layer of NOT gates on the inputs, one AND gate per
accepted string, and an OR gate on top.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers.Depth3

open PEqualNP.CircuitLowerBounds

/-- A block of gates that read only wires already present is evaluated as a map. -/
theorem foldl_block {α : Type} (f : List α → Gate → α)
    (hf : ∀ (w r : List α) (g : Gate), (∀ i ∈ g.inputs, i < w.length) → f (w ++ r) g = f w g)
    (gs : List Gate) (w : List α) (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i < w.length) :
    gs.foldl (fun w g => w ++ [f w g]) w = w ++ gs.map (f w) := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have h' : ∀ g' ∈ gs, ∀ i ∈ g'.inputs, i < (w ++ [f w g]).length := by
      intro g' hg' i hi
      have := h g' (List.mem_cons_of_mem _ hg') i hi
      simp only [List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih _ h']
    have : gs.map (f (w ++ [f w g])) = gs.map (f w) :=
      List.map_congr_left fun g' hg' => hf w _ g' (h g' (List.mem_cons_of_mem _ hg'))
    rw [this]
    simp

/-- The value a gate adds to a list of wire values. -/
def wf (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

/-- The depth a gate adds to a list of wire depths. -/
def df (d : List ℕ) (g : Gate) : ℕ := (g.inputs.map fun i => d.getD i 0).foldr max 0 + 1

theorem getD_append_lt {α : Type} (w r : List α) (i : ℕ) (a : α) (h : i < w.length) :
    (w ++ r).getD i a = w.getD i a := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wf_append (w r : List Bool) (g : Gate) (h : ∀ i ∈ g.inputs, i < w.length) :
    wf (w ++ r) g = wf w g := by
  unfold wf
  congr 1
  exact List.map_congr_left fun i hi => getD_append_lt w r i false (h i hi)

theorem df_append (d r : List ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < d.length) :
    df (d ++ r) g = df d g := by
  unfold df
  congr 2
  exact List.map_congr_left fun i hi => getD_append_lt d r i 0 (h i hi)

theorem getD_le (d : List ℕ) (k i : ℕ) (hd : ∀ a ∈ d, a ≤ k) : d.getD i 0 ≤ k := by
  by_cases h : i < d.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hd _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem df_le (d : List ℕ) (k : ℕ) (hd : ∀ a ∈ d, a ≤ k) (g : Gate) : df d g ≤ k + 1 := by
  unfold df
  have : ∀ l : List ℕ, (l.map fun i => d.getD i 0).foldr max 0 ≤ k := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (getD_le d k i hd) ih
  have := this g.inputs
  omega

theorem block_le (d : List ℕ) (k : ℕ) (hd : ∀ a ∈ d, a ≤ k) (gs : List Gate) :
    ∀ a ∈ d ++ gs.map (df d), a ≤ k + 1 := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact Nat.le_succ_of_le (hd a h)
  · obtain ⟨g, -, rfl⟩ := List.mem_map.1 h
    exact df_le d k hd g

/-- The NOT layer: gate `i` reads input `i`. -/
def nots (n : ℕ) : List Gate := (List.range n).map fun i => ⟨GateOp.not, [i]⟩

/-- The wires read by the AND gate of the string `y`. -/
def lits (n : ℕ) (y : List Bool) : List ℕ :=
  (List.range n).map fun i => if y.getD i false = true then i else n + i

/-- The AND layer: one gate per string. -/
def ands (n : ℕ) (ys : List (List Bool)) : List Gate := ys.map fun y => ⟨GateOp.and, lits n y⟩

/-- The top OR gate, reading the `m` AND gates. -/
def orGate (n m : ℕ) : Gate := ⟨GateOp.or, (List.range m).map fun j => n + n + j⟩

/-- The depth 3 circuit accepting exactly the strings of `ys`. -/
def circ (n : ℕ) (ys : List (List Bool)) : Circuit :=
  ⟨nots n ++ ands n ys ++ [orGate n ys.length], n + n + ys.length⟩

theorem nots_reads (n : ℕ) : ∀ g ∈ nots n, ∀ i ∈ g.inputs, i < n := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  simp only [List.mem_singleton] at hi
  subst hi
  exact List.mem_range.1 hj

theorem ands_reads (n : ℕ) (ys : List (List Bool)) :
    ∀ g ∈ ands n ys, ∀ i ∈ g.inputs, i < n + n := by
  intro g hg i hi
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  have := List.mem_range.1 hj
  split_ifs <;> omega

theorem or_reads (n m : ℕ) : ∀ i ∈ (orGate n m).inputs, i < n + n + m := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
  have := List.mem_range.1 hj
  omega

/-- The three layers, evaluated one block at a time. -/
theorem foldl_circ {α : Type} (f : List α → Gate → α)
    (hf : ∀ (w r : List α) (g : Gate), (∀ i ∈ g.inputs, i < w.length) → f (w ++ r) g = f w g)
    (n : ℕ) (ys : List (List Bool)) (w : List α) (hw : w.length = n) :
    (circ n ys).gates.foldl (fun w g => w ++ [f w g]) w =
      (w ++ (nots n).map (f w)) ++ (ands n ys).map (f (w ++ (nots n).map (f w))) ++
        [f ((w ++ (nots n).map (f w)) ++ (ands n ys).map (f (w ++ (nots n).map (f w))))
          (orGate n ys.length)] := by
  have h1 : ∀ g ∈ nots n, ∀ i ∈ g.inputs, i < w.length := by
    rw [hw]
    exact nots_reads n
  have h2 : ∀ g ∈ ands n ys, ∀ i ∈ g.inputs, i < (w ++ (nots n).map (f w)).length := by
    have : (w ++ (nots n).map (f w)).length = n + n := by simp [hw, nots]
    rw [this]
    exact ands_reads n ys
  simp only [circ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_block f hf _ _ h1, foldl_block f hf _ _ h2]

theorem and_val (x y : List Bool) (hy : y.length = x.length) :
    wf (x ++ (nots x.length).map (wf x)) ⟨GateOp.and, lits x.length y⟩ = true ↔ x = y := by
  have key : ∀ i, i < x.length →
      ((x ++ (nots x.length).map (wf x)).getD
        (if y.getD i false = true then i else x.length + i) false = true ↔
        x.getD i false = y.getD i false) := by
    intro i hi
    by_cases hyi : y.getD i false = true
    · have e : (if y.getD i false = true then i else x.length + i) = i := by
        split_ifs; rfl
      rw [e, getD_append_lt _ _ _ _ hi, hyi]
    · have e : (if y.getD i false = true then i else x.length + i) = x.length + i := by
        split_ifs; rfl
      rw [e]
      have : (x ++ (nots x.length).map (wf x)).getD (x.length + i) false =
          !(x.getD i false) := by
        simp [List.getD_eq_getElem?_getD, nots, wf, GateOp.eval, hi]
      rw [this]
      simp only [Bool.not_eq_true] at hyi
      rw [hyi]
      cases x.getD i false <;> simp
  unfold wf
  simp only [GateOp.eval, lits, List.map_map, List.all_eq_true, List.mem_map, List.mem_range,
    Function.comp]
  constructor
  · intro h
    apply List.ext_getElem hy.symm
    intro i h1 h2
    have := (key i h1).1 (h _ ⟨i, h1, rfl⟩)
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this
  · rintro rfl b ⟨i, hi, rfl⟩
    exact (key i hi).2 rfl

theorem circ_eval (n : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length = n)
    (x : List Bool) (hx : x.length = n) : (circ n ys).eval x = true ↔ x ∈ ys := by
  subst hx
  have hw := foldl_circ wf wf_append x.length ys x rfl
  unfold Circuit.eval Circuit.wires
  change (List.foldl (fun w g => w ++ [wf w g]) x (circ x.length ys).gates).getD _ _ = true ↔ _
  rw [hw]
  set w1 := x ++ (nots x.length).map (wf x) with hw1
  set w2 := w1 ++ (ands x.length ys).map (wf w1) with hw2
  have hl2 : w2.length = x.length + x.length + ys.length := by
    simp only [hw2, hw1, nots, ands, List.length_append, List.length_map, List.length_range]
  have hout : (w2 ++ [wf w2 (orGate x.length ys.length)]).getD (circ x.length ys).output false =
      wf w2 (orGate x.length ys.length) := by
    simp [List.getD_eq_getElem?_getD, circ, ← hl2]
  rw [hout]
  have hj : ∀ j (hj : j < ys.length), w2.getD (x.length + x.length + j) false =
      wf w1 ⟨GateOp.and, lits x.length ys[j]⟩ := by
    intro j hj
    have hl1 : w1.length = x.length + x.length := by simp [hw1, nots]
    rw [hw2, List.getD_eq_getElem?_getD, ← hl1, List.getElem?_append_right (by omega)]
    simp [ands, hj]
  unfold wf
  simp only [orGate, GateOp.eval, List.map_map, List.any_eq_true, List.mem_map, List.mem_range,
    Function.comp]
  constructor
  · rintro ⟨b, ⟨j, hjlt, rfl⟩, hb⟩
    have hb' : w2.getD (x.length + x.length + j) false = true := hb
    rw [hj j hjlt] at hb'
    have := (and_val x ys[j] (hys _ (List.getElem_mem hjlt))).1 hb'
    rw [this]
    exact List.getElem_mem hjlt
  · intro hmem
    obtain ⟨j, hjlt, rfl⟩ := List.getElem_of_mem hmem
    refine ⟨_, ⟨j, hjlt, rfl⟩, ?_⟩
    change w2.getD (ys[j].length + ys[j].length + j) false = true
    rw [hj j hjlt]
    exact (and_val _ _ rfl).2 rfl

theorem circ_depth (n : ℕ) (ys : List (List Bool)) : (circ n ys).depth n ≤ 3 := by
  have hw := foldl_circ df df_append n ys (List.replicate n 0) (by simp)
  unfold Circuit.depth Circuit.depths
  change (List.foldl (fun d g => d ++ [df d g]) (List.replicate n 0) (circ n ys).gates).getD _ _ ≤ 3
  rw [hw]
  apply getD_le
  have h0 : ∀ a ∈ List.replicate n 0, a ≤ 0 := by
    intro a ha
    rw [List.eq_of_mem_replicate ha]
  have h1 := block_le _ 0 h0 (nots n)
  have h2 := block_le _ 1 h1 (ands n ys)
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact Nat.le_succ_of_le (h2 a h)
  · rw [List.mem_singleton.1 h]
    exact df_le _ 2 h2 _

theorem circ_gates (n : ℕ) (ys : List (List Bool)) (hlen : ys.length ≤ 2 ^ n) :
    ∀ g ∈ (circ n ys).gates,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ (n + 2) * 2 ^ n := by
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hb : n + 2 ^ n + 1 ≤ (n + 2) * 2 ^ n := by nlinarith
  intro g hg
  simp only [circ, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | hg) | rfl
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    refine ⟨by simp, ?_⟩
    simp only [List.length_singleton]
    omega
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hg
    refine ⟨by simp, ?_⟩
    simp only [lits, List.length_map, List.length_range]
    omega
  · refine ⟨by simp [orGate], ?_⟩
    simp only [orGate, List.length_map, List.length_range]
    omega

theorem circ_size (n : ℕ) (ys : List (List Bool)) (hlen : ys.length ≤ 2 ^ n) :
    (circ n ys).size ≤ (n + 2) * 2 ^ n := by
  have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hb : n + 2 ^ n + 1 ≤ (n + 2) * 2 ^ n := by nlinarith
  simp only [Circuit.size, circ, nots, ands, List.length_append, List.length_map,
    List.length_range, List.length_singleton]
  omega

/-- All Boolean strings of length `n`. -/
def allStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allStrings n).flatMap fun l => [false :: l, true :: l]

theorem allStrings_length (n : ℕ) : (allStrings n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allStrings, List.length_flatMap, List.length_cons, List.length_nil]
    simp [ih, pow_succ]

theorem mem_allStrings (n : ℕ) (l : List Bool) : l ∈ allStrings n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [allStrings]
  | succ n ih =>
    simp only [allStrings, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨t, ht, rfl | rfl⟩ <;> simp [(ih t).1 ht]
    · intro h
      cases l with
      | nil => simp at h
      | cons b t =>
        refine ⟨t, (ih t).2 (by simpa using h), ?_⟩
        cases b <;> simp

/-- Every language has, at every length, a depth 3 circuit of size `(n + 2) * 2 ^ n`. -/
theorem depth3_universal (L : Language Bool) :
    L ∈ SizeDepth {GateOp.and, GateOp.or, GateOp.not} (fun n : ℕ => (n + 2) * 2 ^ n) 3 := by
  classical
  intro n
  have hlen : ((allStrings n).filter fun y => decide (y ∈ L)).length ≤ 2 ^ n := by
    rw [← allStrings_length n]
    exact List.length_filter_le _ _
  refine ⟨circ n ((allStrings n).filter fun y => decide (y ∈ L)), circ_gates n _ hlen,
    circ_size n _ hlen, circ_depth n _, ?_⟩
  intro x hx
  rw [circ_eval n _ (fun y hy => (mem_allStrings n y).1 (List.mem_filter.1 hy).1) x hx]
  simp [List.mem_filter, mem_allStrings, hx]

end PEqualNP.CircuitLowerBounds.Helpers.Depth3
