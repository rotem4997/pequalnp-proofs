import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4385

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

def bit (i : Fin n) (v : BitVec n) : Bool := v.getLsbD i.val

def gateWord (w : List (BitVec n)) (g : Gate) : (BitVec n) :=
  let args := g.inputs.map fun j => w.getD j 0
  match g.op with
  | .and => args.getD 0 (BitVec.allOnes n) &&& args.getD 1 (BitVec.allOnes n)
  | _ => args.getD 0 0 ||| args.getD 1 0

def wordStep (w : List (BitVec n)) (g : Gate) := w ++ [gateWord w g]

def boolStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

lemma zero_bit (i : Fin n) : (0 : (BitVec n)).getLsbD i.val = false :=
  BitVec.getLsbD_zero

lemma read_bit (w : List (BitVec n)) (i : Fin n) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j 0) := by
  simpa only [bit, zero_bit] using (List.getD_map w 0 (n := j) (bit i))

lemma step_bits (w : List (BitVec n)) (i : Fin n) (g : Gate)
    (hg : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    (wordStep w g).map (bit i) = boolStep (w.map (bit i)) g := by
  obtain ⟨op, args⟩ := g
  change op = .and ∨ op = .or at hg
  change args.length ≤ 2 at hlen
  have shapes : args = [] ∨ (∃ a, args = [a]) ∨ ∃ a b, args = [a, b] := by
    cases args with
    | nil => exact Or.inl rfl
    | cons a tail =>
      cases tail with
      | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
      | cons b tail =>
        cases tail with
        | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
        | cons _ _ => simp at hlen
  rcases hg with rfl | rfl <;>
    rcases shapes with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
    simp only [wordStep, boolStep, gateWord, GateOp.eval, List.map_append, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, read_bit,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, bit,
      BitVec.getLsbD_and, BitVec.getLsbD_or, zero_bit, BitVec.getLsbD_allOnes,
      i.isLt, decide_true, Bool.and_true, Bool.or_false]

lemma run_bits (gs : List Gate) (w : List (BitVec n)) (i : Fin n)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    (gs.foldl wordStep w).map (bit i) = gs.foldl boolStep (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hm g List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun k hk => hm k (List.mem_cons_of_mem g hk)),
      step_bits w i g hop hlen]

def Binary (pool : List (BitVec n)) (v : (BitVec n)) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

def Valid (base values : List (BitVec n)) : Prop :=
  ∀ j (hj : j < values.length), values[j] ∉ base ++ values.take j ∧
    Binary (base ++ values.take j) values[j]

lemma valid_append {base trace : List (BitVec n)} {v : (BitVec n)} (h : Valid base trace)
    (hfresh : v ∉ base ++ trace) (hv : Binary (base ++ trace) v) :
    Valid base (trace ++ [v]) := by
  intro j hj
  by_cases hj' : j < trace.length
  · simpa only [List.getElem_append_left hj',
      List.take_append_of_le_length (Nat.le_of_lt hj')] using h j hj'
  · have heq : j = trace.length := by simp at hj; omega
    subst j
    simpa using And.intro hfresh hv

lemma read_mem {α : Type} {xs pool : List α} (h : xs ⊆ pool) {d : α} (hd : d ∈ pool)
    (i : Nat) : xs.getD i d ∈ pool := by
  rw [List.getD_eq_getElem?_getD]
  cases hv : xs[i]? with
  | none => exact hd
  | some v => exact h (List.mem_of_getElem? hv)

lemma gate_binary {w pool : List (BitVec n)} (g : Gate) (hw : w ⊆ pool)
    (hz : 0 ∈ pool) (ht : BitVec.allOnes n ∈ pool) : Binary pool (gateWord w g) := by
  have hargs : (g.inputs.map fun j => w.getD j 0) ⊆ pool := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    exact read_mem hw hz j
  unfold gateWord
  split
  · exact ⟨_, read_mem hargs ht 0, _, read_mem hargs ht 1, Or.inl rfl⟩
  · exact ⟨_, read_mem hargs hz 0, _, read_mem hargs hz 1, Or.inr rfl⟩

lemma record_step {base trace w : List (BitVec n)} (g : Gate) (hz : 0 ∈ base)
    (ht : BitVec.allOnes n ∈ base) (h : Valid base trace) (hw : w ⊆ base ++ trace) :
    ∃ next : List (BitVec n), next.length ≤ trace.length + 1 ∧ Valid base next ∧
      wordStep w g ⊆ base ++ next := by
  let v := gateWord w g
  by_cases hmem : v ∈ base ++ trace
  · refine ⟨trace, by omega, h, ?_⟩
    exact List.append_subset.mpr ⟨hw, by simpa [v] using hmem⟩
  · have hv := gate_binary g hw (List.mem_append_left _ hz) (List.mem_append_left _ ht)
    refine ⟨trace ++ [v], by simp, valid_append h hmem hv, ?_⟩
    rw [← List.append_assoc]
    exact List.append_subset.mpr ⟨fun _ ha => List.mem_append_left _ (hw ha),
      fun _ ha => List.mem_append_right _ ha⟩

lemma record_run (gs : List Gate) (base trace w : List (BitVec n)) (hz : 0 ∈ base)
    (ht : BitVec.allOnes n ∈ base) (h : Valid base trace) (hw : w ⊆ base ++ trace) :
    ∃ final : List (BitVec n), final.length ≤ trace.length + gs.length ∧ Valid base final ∧
      gs.foldl wordStep w ⊆ base ++ final := by
  induction gs generalizing trace w with
  | nil => exact ⟨trace, by simp, h, hw⟩
  | cons g gs ih =>
    obtain ⟨next, hlen, hnext, hwires⟩ := record_step g hz ht h hw
    obtain ⟨final, hsize, hfinal, hout⟩ := ih next (wordStep w g) hnext hwires
    exact ⟨final, by simp; omega, hfinal, hout⟩

end PEqualNP.Outside.L_meta_4385

open PEqualNP.Outside.L_meta_4385

theorem PEqualNP.Outside.L_meta_4385 : ∀ (x1 : ℕ) (x2 : List (BitVec x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : List (BitVec x1)), x5.length ≤ x3.size ∧ (∀ (x6 : Fin x5.length), ∃ x7 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ List.take (↑x6) x5), ∃ x8 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ List.take (↑x6) x5), x5.get x6 = x7 &&& x8 ∨ x5.get x6 = x7 ||| x8) ∧ ∃ x6 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ x5), ∀ (x7 : Fin x1), x6.getLsbD ↑x7 = x3.eval (List.map (fun (x8 : BitVec x1) => x8.getLsbD ↑x7) x2) := by
  intro n inputs C hm
  let base : List (BitVec n) := 0 :: BitVec.allOnes n :: inputs
  have hinit : inputs ⊆ base ++ [] := by
    intro v hv
    simp [base, hv]
  obtain ⟨trace, hlen, hvalid, hw⟩ := record_run C.gates base [] inputs
    (by simp [base]) (by simp [base]) (by intro j hj; simp at hj) hinit
  let wires := C.gates.foldl wordStep inputs
  refine ⟨trace, by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hlen, ?_,
    wires.getD C.output 0, ?_, ?_⟩
  · intro j
    exact (hvalid j.val j.isLt).2
  · exact read_mem hw (List.mem_append_left _ (by simp [base])) C.output
  · intro i
    change bit i (wires.getD C.output 0) = _
    rw [← read_bit]
    change ((C.gates.foldl wordStep inputs).map (bit i)).getD C.output false =
      (C.gates.foldl boolStep (inputs.map (bit i))).getD C.output false
    rw [run_bits C.gates inputs i hm]
