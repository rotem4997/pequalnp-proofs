import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_544_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

lemma run_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ hi

def orWire (n d k : ℕ) : ℕ :=
  if k = 0 then n else n + (d + 1) + (k - 1)

def orChain (n d : ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => orChain n d k ++ [⟨GateOp.or, [orWire n d k, n + (k + 1)]⟩]

lemma orChain_length (n d k : ℕ) : (orChain n d k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [orChain, ih]

lemma orChain_fanInTwo (n d k : ℕ) :
    ∀ g ∈ orChain n d k,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => simp [orChain]
  | succ k ih =>
    intro g hg
    simp only [orChain, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact ih g h
    · exact ⟨by simp, by simp⟩

lemma orWire_lt (n d k : ℕ) : orWire n d k < n + (d + 1) + k := by
  unfold orWire
  split_ifs <;> omega

lemma orChain_eval (n d : ℕ) (x : Fin (n + (d + 1)) → Bool) :
    ∀ k ≤ d,
      (run (orChain n d k) (List.ofFn x)).getD (orWire n d k) false =
        decide (∃ j : Fin (d + 1), j.val ≤ k ∧ x (Fin.natAdd n j) = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [orChain, orWire, ↓reduceIte, run, List.foldl_nil]
    rw [getD_ofFn x n (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨⟨0, by omega⟩, le_rfl, ?_⟩
      simpa [Fin.natAdd] using h
    · rintro ⟨j, hj, hxj⟩
      have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hj0] at hxj
      simpa [Fin.natAdd] using hxj
  | succ k ih =>
    intro hk1
    have hkd : k ≤ d := by omega
    rw [orChain, run_append]
    set W := run (orChain n d k) (List.ofFn x)
    have hW_len : W.length = n + (d + 1) + k := by
      rw [show W = run (orChain n d k) (List.ofFn x) from rfl,
        run_length, List.length_ofFn, orChain_length]
    have hwire_eq : orWire n d (k + 1) = W.length := by
      simp [orWire, hW_len]
    change (step W ⟨GateOp.or, [orWire n d k, n + (k + 1)]⟩).getD (orWire n d (k + 1)) false = _
    rw [hwire_eq, step, getD_snoc_eq]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false]
    rw [ih hkd]
    have hprev : W.getD (n + (k + 1)) false = x ⟨n + (k + 1), by omega⟩ := by
      rw [show W = run (orChain n d k) (List.ofFn x) from rfl,
        run_getD_of_lt _ _ (n + (k + 1)) (by simp [List.length_ofFn]; omega),
        getD_ofFn x (n + (k + 1)) (by omega)]
    rw [hprev]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨j, hj, hxj⟩ | hx)
      · exact ⟨j, by omega, hxj⟩
      · refine ⟨⟨k + 1, by omega⟩, le_rfl, ?_⟩
        simpa [Fin.natAdd] using hx
    · rintro ⟨j, hj, hxj⟩
      by_cases hjk : j.val ≤ k
      · exact Or.inl ⟨j, hjk, hxj⟩
      · have hjeq : j = ⟨k + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hjeq] at hxj
        exact Or.inr (by simpa [Fin.natAdd] using hxj)

def remapIdx (n d : ℕ) (i : ℕ) : ℕ :=
  if i < n then i else if i = n then orWire n d d else i + 2 * d

def remapGate (n d : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapIdx n d)⟩

lemma run_remap (n d : ℕ) (gs : List Gate) (w₁ w₂ : List Bool)
    (h1 : n + 1 ≤ w₁.length) (h2 : w₂.length = w₁.length + 2 * d)
    (hagree : ∀ i, w₂.getD (remapIdx n d i) false = w₁.getD i false) :
    ∀ i, (run (gs.map (remapGate n d)) w₂).getD (remapIdx n d i) false =
      (run gs w₁).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hagree
  | cons g gs ih =>
    simp only [List.map_cons]
    change ∀ i, (run (gs.map (remapGate n d)) (step w₂ (remapGate n d g))).getD (remapIdx n d i) false =
      (run gs (step w₁ g)).getD i false
    apply ih (step w₁ g) (step w₂ (remapGate n d g))
    · simp [step]; omega
    · simp [step]; omega
    · intro i
      have heval : (remapGate n d g).op.eval ((remapGate n d g).inputs.map fun j => w₂.getD j false) =
          g.op.eval (g.inputs.map fun j => w₁.getD j false) := by
        simp only [remapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact hagree j
      by_cases hlt : i < w₁.length
      · have hlt' : remapIdx n d i < w₂.length := by
          unfold remapIdx
          have hw := orWire_lt n d d
          split_ifs <;> omega
        rw [step, step, getD_snoc_lt _ _ _ hlt', getD_snoc_lt _ _ _ hlt]
        exact hagree i
      · by_cases heq : i = w₁.length
        · subst heq
          have hrm : remapIdx n d w₁.length = w₂.length := by
            unfold remapIdx
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          rw [hrm, step, step, getD_snoc_eq, getD_snoc_eq, heval]
        · have hge1 : (step w₁ g).length ≤ i := by simp [step]; omega
          have hge2 : (step w₂ (remapGate n d g)).length ≤ remapIdx n d i := by
            unfold remapIdx
            split_ifs <;> simp [step] <;> omega
          rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]

end PEqualNP.Outside.L_meta_544_aux

theorem PEqualNP.Outside.L_meta_544 :
    ∀ (n d s : ℕ) (g : (Fin n → Bool) → Bool) (v : Fin n),
      PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool =>
          g (fun i : Fin n => x i.castSucc) || (x v.castSucc && x (Fin.last n))) s →
      PEqualNP.MetaComplexity.HasCircuitSize (n + (d + 1))
        (fun x : Fin (n + (d + 1)) → Bool =>
          g (fun i : Fin n => x (Fin.castAdd (d + 1) i)) ||
            (x (Fin.castAdd (d + 1) v) && decide (∃ j : Fin (d + 1), x (Fin.natAdd n j) = true)))
        (s + d) := by
  intro n d s g v ⟨C, hfan, hsize, heval⟩
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_544_aux in
  let C' : Circuit := ⟨orChain n d d ++ C.gates.map (remapGate n d), remapIdx n d C.output⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro gate hgate
    simp only [C', List.mem_append, List.mem_map] at hgate
    rcases hgate with h1 | ⟨g0, hg0, rfl⟩
    · exact orChain_fanInTwo n d d gate h1
    · obtain ⟨hop, hlen⟩ := hfan g0 hg0
      exact ⟨hop, by simpa [remapGate] using hlen⟩
  · change C'.gates.length ≤ s + d
    change C.gates.length ≤ s at hsize
    simp only [C', List.length_append, List.length_map, orChain_length]
    omega
  · intro x
    let y : Fin (n + 1) → Bool := fun i =>
      if h : i.val < n then x (Fin.castAdd (d + 1) ⟨i.val, h⟩)
      else decide (∃ j : Fin (d + 1), x (Fin.natAdd n j) = true)
    set W0 := run (orChain n d d) (List.ofFn x)
    have hW0_len : W0.length = n + (d + 1) + d := by
      rw [show W0 = run (orChain n d d) (List.ofFn x) from rfl,
        run_length, List.length_ofFn, orChain_length]
    have hW0_or : W0.getD (orWire n d d) false =
        decide (∃ j : Fin (d + 1), x (Fin.natAdd n j) = true) := by
      rw [show W0 = run (orChain n d d) (List.ofFn x) from rfl, orChain_eval n d x d le_rfl]
      congr 1
      apply propext
      constructor
      · rintro ⟨j, _, hxj⟩; exact ⟨j, hxj⟩
      · rintro ⟨j, hxj⟩; exact ⟨j, by omega, hxj⟩
    have hbase : ∀ i, W0.getD (remapIdx n d i) false = (List.ofFn y).getD i false := by
      intro i
      unfold remapIdx
      by_cases hi : i < n
      · rw [if_pos hi]
        rw [show W0 = run (orChain n d d) (List.ofFn x) from rfl,
          run_getD_of_lt _ _ i (by simp [List.length_ofFn]; omega),
          getD_ofFn x i (by omega), getD_ofFn y i (by omega)]
        simp [y, hi, Fin.castAdd]
      · rw [if_neg hi]
        by_cases heq : i = n
        · rw [heq, if_pos rfl, hW0_or, getD_ofFn y n (by omega)]
          simp [y]
        · rw [if_neg heq]
          rw [List.getD_eq_default W0 _ (by omega),
            List.getD_eq_default (List.ofFn y) _ (by simp [List.length_ofFn]; omega)]
    have hrem := run_remap n d C.gates (List.ofFn y) W0 (by simp) (by simp [hW0_len]; omega) hbase
    have hC'_eval : C'.eval (List.ofFn x) = C.eval (List.ofFn y) := by
      change (run (orChain n d d ++ C.gates.map (remapGate n d)) (List.ofFn x)).getD
          (remapIdx n d C.output) false = (run C.gates (List.ofFn y)).getD C.output false
      rw [run_append]
      exact hrem C.output
    rw [hC'_eval, heval y]
    have hy_cast : (fun i : Fin n => y i.castSucc) = fun i : Fin n => x (Fin.castAdd (d + 1) i) := by
      funext i
      simp only [y, Fin.val_castSucc, i.isLt, ↓reduceDIte]
    have hy_v : y v.castSucc = x (Fin.castAdd (d + 1) v) := by
      simp only [y, Fin.val_castSucc, v.isLt, ↓reduceDIte]
    have hy_last : y (Fin.last n) = decide (∃ j : Fin (d + 1), x (Fin.natAdd n j) = true) := by
      simp [y]
    dsimp only
    rw [hy_cast, hy_v, hy_last]
