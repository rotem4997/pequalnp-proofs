import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2776

open PEqualNP.CircuitLowerBounds

abbrev Word := BitVec 24

def inputs : List Word :=
  [4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888,
   16646144, 13339321]

def seeds : List Word := 0 :: BitVec.allOnes 24 :: inputs

def rows : List Nat :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201,
   208, 261, 264, 276, 288, 320, 385, 402]

def positives : List Nat := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def assignment (row : Nat) : List Bool :=
  let x := fun i : Fin 9 => row.testBit i.val
  List.ofFn x ++ [x 0 || x 4]

def bit (i : Fin 24) (v : Word) : Bool := v.getLsbD i.val

lemma row_data : ∀ i : Fin 24, rows.getD i.val 0 ∈ rows ∧
    inputs.map (bit i) = assignment (rows.getD i.val 0) ∧
    bit i 3428671 = decide (rows.getD i.val 0 ∈ positives) := by decide

def gateWord (w : List Word) (g : Gate) : Word :=
  let args := g.inputs.map fun j => w.getD j 0
  match g.op with
  | .and => args.getD 0 (BitVec.allOnes 24) &&& args.getD 1 (BitVec.allOnes 24)
  | _ => args.getD 0 0 ||| args.getD 1 0

def wordStep (w : List Word) (g : Gate) := w ++ [gateWord w g]

def boolStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

lemma zero_bit (i : Fin 24) : (0 : Word).getLsbD i.val = false :=
  BitVec.getLsbD_zero

lemma read_bit (w : List Word) (i : Fin 24) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j 0) := by
  simpa only [bit, zero_bit] using (List.getD_map w 0 (n := j) (bit i))

lemma step_bits (w : List Word) (i : Fin 24) (g : Gate)
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

lemma run_bits (gs : List Gate) (w : List Word) (i : Fin 24)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    (gs.foldl wordStep w).map (bit i) = gs.foldl boolStep (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hm g List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun k hk => hm k (List.mem_cons_of_mem g hk)),
      step_bits w i g hop hlen]

def Binary (pool : List Word) (v : Word) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool, v = a &&& b ∨ v = a ||| b

def Valid (base values : List Word) : Prop :=
  ∀ j (hj : j < values.length), values[j] ∉ base ++ values.take j ∧
    Binary (base ++ values.take j) values[j]

lemma valid_append {base trace : List Word} {v : Word} (h : Valid base trace)
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

lemma gate_binary {w pool : List Word} (g : Gate) (hw : w ⊆ pool)
    (hz : 0 ∈ pool) (ht : BitVec.allOnes 24 ∈ pool) : Binary pool (gateWord w g) := by
  have hargs : (g.inputs.map fun j => w.getD j 0) ⊆ pool := by
    intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    exact read_mem hw hz j
  unfold gateWord
  split
  · exact ⟨_, read_mem hargs ht 0, _, read_mem hargs ht 1, Or.inl rfl⟩
  · exact ⟨_, read_mem hargs hz 0, _, read_mem hargs hz 1, Or.inr rfl⟩

lemma record_step {base trace w : List Word} (g : Gate) (hz : 0 ∈ base)
    (ht : BitVec.allOnes 24 ∈ base) (h : Valid base trace) (hw : w ⊆ base ++ trace) :
    ∃ next : List Word, next.length ≤ trace.length + 1 ∧ Valid base next ∧
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

lemma record_run (gs : List Gate) (base trace w : List Word) (hz : 0 ∈ base)
    (ht : BitVec.allOnes 24 ∈ base) (h : Valid base trace) (hw : w ⊆ base ++ trace) :
    ∃ final : List Word, final.length ≤ trace.length + gs.length ∧ Valid base final ∧
      gs.foldl wordStep w ⊆ base ++ final := by
  induction gs generalizing trace w with
  | nil => exact ⟨trace, by simp, h, hw⟩
  | cons g gs ih =>
    obtain ⟨next, hlen, hnext, hwires⟩ := record_step g hz ht h hw
    obtain ⟨final, hsize, hfinal, hout⟩ := ih next (wordStep w g) hnext hwires
    exact ⟨final, by simp; omega, hfinal, hout⟩

end PEqualNP.Outside.L_meta_2776

open PEqualNP.Outside.L_meta_2776

theorem PEqualNP.Outside.L_meta_2776 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       have x4 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];       ∃ (x5 : List (BitVec (24 : ℕ))), x5.length ≤ x1.size ∧ (∀ (x6 : ℕ) (x7 : x6 < x5.length), x5[x6] ∉ x4 ++ List.take x6 x5 ∧ ∃ x8 ∈ x4 ++ List.take x6 x5, ∃ x9 ∈ x4 ++ List.take x6 x5, x5[x6] = x8 &&& x9 ∨ x5[x6] = x8 ||| x9) ∧ (3428671 : BitVec (24 : ℕ)) ∈ x4 ++ x5 := by
  intro C hm hrows
  change ∀ row ∈ rows, C.eval (assignment row) = decide (row ∈ positives) at hrows
  have hinit : inputs ⊆ seeds ++ [] := by
    intro v hv
    simp [seeds, hv]
  obtain ⟨trace, hlen, hvalid, hw⟩ := record_run C.gates seeds [] inputs
    (by simp [seeds]) (by simp [seeds]) (by intro j hj; simp at hj) hinit
  let wires := C.gates.foldl wordStep inputs
  have houtput : wires.getD C.output 0 = 3428671 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin 24 := ⟨j, hj⟩
    obtain ⟨hrow, hin, hout⟩ := row_data i
    change bit i (wires.getD C.output 0) = bit i 3428671
    rw [← read_bit, hout, ← hrows _ hrow]
    change ((C.gates.foldl wordStep inputs).map (bit i)).getD C.output false =
      (C.gates.foldl boolStep (assignment (rows.getD i.val 0))).getD C.output false
    rw [run_bits C.gates inputs i hm, hin]
  refine ⟨trace, by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hlen, hvalid, ?_⟩
  change (3428671 : Word) ∈ seeds ++ trace
  rw [← houtput]
  exact read_mem hw (List.mem_append_left _ (by simp [seeds])) C.output
