import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_152_aux

open PEqualNP.CircuitLowerBounds

-- The wire induction and AND-gate records are adapted from L-meta-702.
def W (gs : List Gate) (x : Fin 4 → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

def wf (gs : List Gate) (k : ℕ) : (Fin 4 → Bool) → Bool :=
  fun x => (W gs x).getD k false

private theorem fold_len (gs : List Gate) : ∀ w0 : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs with
  | nil => intro w0; simp
  | cons g gs ih => intro w0; rw [List.foldl_cons, ih]; simp; omega

theorem W_len (gs : List Gate) (x : Fin 4 → Bool) :
    (W gs x).length = 4 + gs.length := by
  unfold W
  rw [fold_len]
  simp

theorem W_snoc (gs : List Gate) (g : Gate) (x : Fin 4 → Bool) :
    W (gs ++ [g]) x
      = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem wf_snoc (gs : List Gate) (g : Gate) (k : ℕ) :
    wf (gs ++ [g]) k = if k = 4 + gs.length then
      (fun x => g.op.eval (g.inputs.map fun i => wf gs i x)) else wf gs k := by
  funext x
  have hl := W_len gs x
  by_cases hk : k = 4 + gs.length
  · rw [if_pos hk]
    show (W (gs ++ [g]) x).getD k false = g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
    rw [W_snoc]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl, hk]
  · rw [if_neg hk]
    show (W (gs ++ [g]) x).getD k false = (W gs x).getD k false
    rw [W_snoc]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
    split
    · rfl
    · rename_i h2
      have h3 : ¬ (k - (4 + gs.length) = 0) := by omega
      have h4 : ¬ k < (W gs x).length := by rw [hl]; exact h2
      simp [h3, hl, h2]

-- For each AND gate record the first operand on a given input. Inputs with
-- identical records cannot have two false outputs and a true output on their union.
def boundedBit (z x y : Bool) := z = true → x = true ∨ y = true

lemma bounded_gate (g : Gate) (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z x y : ℕ → Bool) (h : ∀ k, boundedBit (z k) (x k) (y k))
    (same : g.op = GateOp.and → x (g.inputs.headD 0) = y (g.inputs.headD 0)) :
    boundedBit (g.op.eval (g.inputs.map z)) (g.op.eval (g.inputs.map x)) (g.op.eval (g.inputs.map y)) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,len⟩ := hm
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at len
  cases ins with
  | nil => rcases hop with rfl|rfl <;> simp [boundedBit,GateOp.eval]
  | cons i tail =>
    cases tail with
    | nil => rcases hop with rfl|rfl <;> simpa [GateOp.eval] using h i
    | cons j rest =>
      cases rest with
      | cons l t => simp at len
      | nil =>
        have hi := h i
        have hj := h j
        rcases hop with rfl|rfl
        · have e : x i = y i := same rfl
          simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,id_eq,
            Bool.and_true,boundedBit,Bool.and_eq_true,e] at hi hj ⊢
          tauto
        · simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,
            Bool.or_false,boundedBit,Bool.or_eq_true] at hi hj ⊢
          tauto

def joinInput (x y : Fin 4 → Bool) := fun i => x i || y i

lemma bounded_wires (gs : List Gate) (x y : Fin 4 → Bool)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (record : ∀ j g, gs[j]? = some g → g.op = GateOp.and →
      wf (gs.take j) (g.inputs.headD 0) x = wf (gs.take j) (g.inputs.headD 0) y) :
    ∀ k, boundedBit (wf gs k (joinInput x y)) (wf gs k x) (wf gs k y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k
    by_cases hk : k < 4
    · interval_cases k <;> simp [wf, W, joinInput, boundedBit]
    · simp [wf,W,List.getD_eq_getElem?_getD,hk,boundedBit]
  | append_singleton gs g ih =>
    have prev := ih (fun a ha => hm a (by simp [ha])) (by
      intro j a hj hop
      have hjl := (List.getElem?_eq_some_iff.mp hj).1
      have h := record j a (by rw [List.getElem?_append_left hjl]; exact hj) hop
      simpa [List.take_append_of_le_length (Nat.le_of_lt hjl)] using h)
    intro k
    rw [wf_snoc]
    split
    · have eq (hop : g.op = GateOp.and) := record gs.length g (by simp) hop
      exact bounded_gate g (hm g (by simp)) _ _ _ prev (by simpa using eq)
    · exact prev k


-- The independent sets are {0,2}, {0,3}, and {1,3}.
def sample (r : Fin 3) (i : Fin 4) : Bool :=
  (([5, 9, 10] : List ℕ).getD r.val 0).testBit i.val

abbrev hasEdge (x : Fin 4 → Bool) :=
  ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true

lemma independent : ∀ r, ¬ hasEdge (sample r) := by decide

lemma pair_union : ∀ r s, r ≠ s → hasEdge (joinInput (sample r) (sample s)) := by decide

end PEqualNP.Outside.L_meta_152_aux

open PEqualNP.Outside.L_meta_152_aux

theorem PEqualNP.Outside.L_meta_152 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) := by
  classical
  rintro ⟨C, hm, ⟨A, hsize, hgate⟩, correct⟩
  let record (r : Fin 3) (j : A) : Bool :=
    (C.gates[j.val]?).elim false (fun g => wf (C.gates.take j.val) (g.inputs.headD 0) (sample r))
  have injective : Function.Injective record := by
    intro r s heq
    by_contra distinct
    have bounds := bounded_wires C.gates (sample r) (sample s) (fun g hg => by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm g hg) (by
      intro j g hj hop
      have eq := congrFun heq (⟨j, hgate j g hj hop⟩ : A)
      simpa [record, hj] using eq) C.output
    have union_true := (correct _).mpr (pair_union r s distinct)
    rcases bounds union_true with left | right
    · exact independent r ((correct _).mp left)
    · exact independent s ((correct _).mp right)
  have count := Fintype.card_le_of_injective _ injective
  have lower : 3 ≤ 2 ^ A.card := by simpa [Fintype.card_fun] using count
  have upper := Nat.pow_le_pow_right (by decide : 0 < 2) hsize
  omega
