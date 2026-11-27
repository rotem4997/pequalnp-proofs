import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_foldl (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem getD_snoc_eq (L : List Bool) (S d : Bool) (k : ℕ) (hk : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst hk
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_lt (L : List Bool) (S d : Bool) (j : ℕ) (hj : j < L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem getD_big (L : List Bool) (d : Bool) (j : ℕ) (hj : L.length ≤ j) : L.getD j d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

/-- The index of a wire after one input is added at position `n`. -/
def sh (n i : ℕ) : ℕ := if i < n then i else i + 1

def shG (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n)⟩

def Inv (n : ℕ) (z : Bool) (w w' : List Bool) : Prop :=
  w'.length = w.length + 1 ∧ n ≤ w.length ∧ w'.getD n false = z ∧
    ∀ i, w'.getD (sh n i) false = w.getD i false

theorem inv_step {n : ℕ} {z : Bool} {w w' : List Bool} (h : Inv n z w w') (g : Gate) :
    Inv n z (step w g) (step w' (shG n g)) := by
  obtain ⟨hl, hn, hz, hi⟩ := h
  have hv : (shG n g).op.eval ((shG n g).inputs.map fun i => w'.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [shG, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hi i
  refine ⟨by simp [step, hl], by simp [step]; omega, ?_, ?_⟩
  · simp only [step]
    rw [getD_snoc_lt _ _ _ _ (by omega)]
    exact hz
  · intro i
    simp only [step, hv]
    by_cases h1 : i < w.length
    · have h2 : sh n i < w'.length := by
        unfold sh
        split <;> omega
      rw [getD_snoc_lt _ _ _ _ h2, getD_snoc_lt _ _ _ _ h1]
      exact hi i
    · by_cases h2 : i = w.length
      · have h3 : sh n i = w'.length := by
          unfold sh
          split <;> omega
        rw [h3, getD_snoc_eq _ _ _ _ rfl, h2, getD_snoc_eq _ _ _ _ rfl]
      · have h3 : w'.length + 1 ≤ sh n i := by
          unfold sh
          split <;> omega
        rw [getD_big _ _ _ (by simp <;> omega), getD_big _ _ _ (by simp <;> omega)]

theorem inv_foldl {n : ℕ} {z : Bool} (gs : List Gate) : ∀ {w w' : List Bool}, Inv n z w w' →
    Inv n z (gs.foldl step w) ((gs.map (shG n)).foldl step w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' h
    exact ih (inv_step h g)

theorem inv_init (n : ℕ) (z : Bool) (y : List Bool) (hy : y.length = n) :
    Inv n z y (y ++ [z]) := by
  refine ⟨by simp, by omega, getD_snoc_eq _ _ _ _ hy, ?_⟩
  intro i
  by_cases h : i < n
  · have : sh n i = i := by simp [sh, h]
    rw [this, getD_snoc_lt _ _ _ _ (by omega)]
  · have : sh n i = i + 1 := by simp [sh, h]
    rw [this, getD_big _ _ _ (by simp <;> omega), getD_big _ _ _ (by omega)]

theorem ofFn_last (n : ℕ) (x : Fin (n + 1) → Bool) :
    List.ofFn x = List.ofFn (fun i : Fin n => x i.castSucc) ++ [x (Fin.last n)] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

/-- The four gates above `g`: `(z OR g) AND NOT (z AND g)`. -/
def tailA (m n p : ℕ) : List Gate :=
  [⟨GateOp.or, [n, p]⟩, ⟨GateOp.and, [n, p]⟩, ⟨GateOp.not, [m + 1]⟩, ⟨GateOp.and, [m, m + 2]⟩]

/-- The four gates above `h = NOT g`: `(z AND h) OR NOT (z OR h)`. -/
def tailB (m n p : ℕ) : List Gate :=
  [⟨GateOp.and, [n, p]⟩, ⟨GateOp.or, [n, p]⟩, ⟨GateOp.not, [m + 1]⟩, ⟨GateOp.or, [m, m + 2]⟩]

theorem tailA_val (L : List Bool) (m n p : ℕ) (hm : L.length = m) (hn : n < m) (hp : p < m) :
    ((tailA m n p).foldl step L).getD (m + 3) false
      = ((L.getD n false || L.getD p false) && !(L.getD n false && L.getD p false)) := by
  subst hm
  simp only [tailA, List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, List.headD_cons,
    Bool.and_true, Bool.or_false]
  rw [getD_snoc_eq _ _ _ _ (by simp <;> omega)]
  rw [getD_snoc_lt _ _ _ _ (by simp <;> omega), getD_snoc_lt _ _ _ _ (by simp <;> omega),
    getD_snoc_eq _ _ _ _ rfl]
  rw [getD_snoc_eq _ _ _ _ (by simp)]
  rw [getD_snoc_eq _ _ _ _ (by simp)]
  rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]

theorem tailB_val (L : List Bool) (m n p : ℕ) (hm : L.length = m) (hn : n < m) (hp : p < m) :
    ((tailB m n p).foldl step L).getD (m + 3) false
      = ((L.getD n false && L.getD p false) || !(L.getD n false || L.getD p false)) := by
  subst hm
  simp only [tailB, List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil,
    GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, List.headD_cons,
    Bool.and_true, Bool.or_false]
  rw [getD_snoc_eq _ _ _ _ (by simp <;> omega)]
  rw [getD_snoc_lt _ _ _ _ (by simp <;> omega), getD_snoc_lt _ _ _ _ (by simp <;> omega),
    getD_snoc_eq _ _ _ _ rfl]
  rw [getD_snoc_eq _ _ _ _ (by simp)]
  rw [getD_snoc_eq _ _ _ _ (by simp)]
  rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]


theorem not_val (L : List Bool) (m n : ℕ) (hm : L.length = m) :
    (([⟨GateOp.not, [n]⟩] : List Gate).foldl step L).getD m false = !(L.getD n false) := by
  simp only [List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil, GateOp.eval,
    List.headD_cons]
  rw [getD_snoc_eq _ _ _ _ hm]

theorem fan_map (n : ℕ) (C : Circuit) (hf : FanInTwo C) (T : List Gate)
    (hT : ∀ g ∈ T, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) (o : ℕ) :
    FanInTwo ⟨C.gates.map (shG n) ++ T, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with h1 | h1
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
    have := hf g0 hg0
    simpa [shG] using this
  · exact hT g h1

theorem tailA_ok (m n p : ℕ) : ∀ g ∈ tailA m n p,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [tailA, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem tailB_ok (m n p : ℕ) : ∀ g ∈ tailB m n p,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [tailB, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

/-- What the shifted circuit computes: the old wires, with the fresh input at position `n`. -/
theorem shifted (n : ℕ) (C : Circuit) (x : Fin (n + 1) → Bool) :
    ((C.gates.map (shG n)).foldl step (List.ofFn x)).length = n + 1 + C.gates.length ∧
    ((C.gates.map (shG n)).foldl step (List.ofFn x)).getD n false = x (Fin.last n) ∧
    ((C.gates.map (shG n)).foldl step (List.ofFn x)).getD (sh n C.output) false
      = C.eval (List.ofFn fun i : Fin n => x i.castSucc) := by
  have hinv := inv_foldl (z := x (Fin.last n)) C.gates
    (inv_init n (x (Fin.last n)) (List.ofFn fun i : Fin n => x i.castSucc) (by simp))
  rw [← ofFn_last] at hinv
  obtain ⟨hl, -, hz, hi⟩ := hinv
  have hlen := len_foldl C.gates (List.ofFn fun i : Fin n => x i.castSucc)
  simp only [List.length_ofFn] at hlen
  refine ⟨by rw [hl, hlen]; omega, hz, ?_⟩
  rw [hi, Circuit.eval, wires_eq]

theorem main1 (n s : ℕ) (g : (Fin n → Bool) → Bool) (h : HasCircuitSize n g s) :
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool =>
      xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4) := by
  obtain ⟨C, hf, hs, he⟩ := h
  by_cases ho : C.output < n + C.gates.length
  · refine ⟨⟨C.gates.map (shG n) ++ tailA (n + 1 + C.gates.length) n (sh n C.output),
      n + 1 + C.gates.length + 3⟩, fan_map n C hf _ (tailA_ok _ _ _) _, ?_, ?_⟩
    · simp only [Circuit.size, List.length_append, List.length_map, tailA, List.length_cons,
        List.length_nil] at hs ⊢
      omega
    · intro x
      obtain ⟨hl, hz, hv⟩ := shifted n C x
      show (List.foldl step (List.ofFn x) _).getD _ false = _
      beta_reduce
      rw [List.foldl_append, tailA_val _ _ _ _ hl (by omega) (by unfold sh; split <;> omega),
        hz, hv, he]
      cases x (Fin.last n) <;> cases g (fun i : Fin n => x i.castSucc) <;> rfl
  · have hg0 : ∀ y : Fin n → Bool, g y = false := by
      intro y
      rw [← he y, Circuit.eval, wires_eq]
      exact getD_big _ _ _ (by rw [len_foldl]; simp; omega)
    refine ⟨⟨C.gates.map (shG n), n⟩, ?_, ?_, ?_⟩
    · have := fan_map n C hf [] (by simp) n
      simpa using this
    · simp only [Circuit.size, List.length_map] at hs ⊢
      omega
    · intro x
      obtain ⟨-, hz, -⟩ := shifted n C x
      show (List.foldl step (List.ofFn x) _).getD _ false = _
      beta_reduce
      rw [hz, hg0]
      simp

theorem main2 (n s : ℕ) (g : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s) :
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool =>
      xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4) := by
  obtain ⟨C, hf, hs, he⟩ := h
  by_cases ho : C.output < n + C.gates.length
  · refine ⟨⟨C.gates.map (shG n) ++ tailB (n + 1 + C.gates.length) n (sh n C.output),
      n + 1 + C.gates.length + 3⟩, fan_map n C hf _ (tailB_ok _ _ _) _, ?_, ?_⟩
    · simp only [Circuit.size, List.length_append, List.length_map, tailB, List.length_cons,
        List.length_nil] at hs ⊢
      omega
    · intro x
      obtain ⟨hl, hz, hv⟩ := shifted n C x
      show (List.foldl step (List.ofFn x) _).getD _ false = _
      beta_reduce
      rw [List.foldl_append, tailB_val _ _ _ _ hl (by omega) (by unfold sh; split <;> omega),
        hz, hv, he]
      beta_reduce
      cases x (Fin.last n) <;> cases g (fun i : Fin n => x i.castSucc) <;> rfl
  · have hg0 : ∀ y : Fin n → Bool, g y = true := by
      intro y
      have h2 := he y
      rw [Circuit.eval, wires_eq, getD_big _ _ _ (by rw [len_foldl]; simp <;> omega)] at h2
      simpa using h2.symm
    refine ⟨⟨C.gates.map (shG n) ++ [⟨GateOp.not, [n]⟩], n + 1 + C.gates.length⟩,
      fan_map n C hf _ (by simp) _, ?_, ?_⟩
    · simp only [Circuit.size, List.length_append, List.length_map, List.length_cons,
        List.length_nil] at hs ⊢
      omega
    · intro x
      obtain ⟨hl, hz, -⟩ := shifted n C x
      show (List.foldl step (List.ofFn x) _).getD _ false = _
      beta_reduce
      rw [List.foldl_append, not_val _ _ _ hl, hz, hg0]
      simp

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 : ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool), (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) :=
  fun n s g => ⟨PEqualNP.Outside.L_meta_716.main1 n s g, PEqualNP.Outside.L_meta_716.main2 n s g⟩
