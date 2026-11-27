import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3320_aux

open CircuitLowerBounds

abbrev E (p l : Fin 4) : Prop :=
  ((p, l) ∈ ([(0, 0), (1, 0), (0, 1), (0, 2), (1, 3), (2, 0), (3, 1)] : List (Fin 4 × Fin 4)))

abbrev edgeOn (x : Fin 8 → Bool) : Prop :=
  ∃ p l : Fin 4, E p l ∧ x (Fin.castAdd 4 p) = true ∧ x (Fin.natAdd 4 l) = true

def C : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.and, [10, 0]⟩,
  ⟨.and, [10, 4]⟩,
  ⟨.or, [11, 12]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.and, [8, 14]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [16, 17]⟩,
  ⟨.and, [15, 18]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.and, [20, 9]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [3, 4]⟩,
  ⟨.and, [22, 23]⟩,
  ⟨.and, [21, 24]⟩,
  ⟨.or, [19, 25]⟩,
  ⟨.or, [13, 26]⟩], 27⟩

def C0 : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (fun i => if i = 8 + 2 then 8 + C.size else i)⟩), C.output⟩

def pairInput (p l : Fin 4) : Fin 8 → Bool :=
  fun i => decide (i = Fin.castAdd 4 p) || decide (i = Fin.natAdd 4 l)

def Z (i : ℕ) : Prop := ∀ x : Fin 8 → Bool, (C0.wires (List.ofFn x)).getD i false = false

def bitInput (m : ℕ) : Fin 8 → Bool := fun i => m.testBit i.val

def oldGate (k : ℕ) : Gate := C.gates.getD k ⟨.or, []⟩

def left (k : ℕ) : ℕ := (oldGate k).inputs.getD 0 0

def right (k : ℕ) : ℕ := (oldGate k).inputs.getD 1 0

def replacement (k : ℕ) (m : Fin 3) : Gate :=
  if m = 0 then ⟨.and, [left k]⟩ else
    if m = 1 then ⟨.and, [right k]⟩ else
      match (oldGate k).op with
      | .and => ⟨.or, []⟩
      | _ => ⟨.and, []⟩

def mutationWitnesses : List (List ℕ) := [
  [242, 241, 240], [236, 220, 204], [141, 240, 177], [102, 141, 165], [102, 240, 114],
  [114, 165, 240], [166, 79, 15], [15, 240, 230], [230, 79, 102], [205, 166, 141],
  [141, 102, 230], [141, 240, 230], [248, 244, 240], [204, 240, 252], [248, 220, 216],
  [244, 236, 228], [228, 216, 252], [228, 240, 252], [252, 230, 240], [252, 177, 240]]

def witness (k : ℕ) (m : Fin 3) : Fin 8 → Bool :=
  bitInput ((mutationWitnesses.getD k []).getD m.val 0)

def changed (k : ℕ) (g : Gate) : Circuit := ⟨C.gates.set k g, C.output⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma complete : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = true ↔ edgeOn x := by
  decide +kernel

set_option maxHeartbeats 5000000 in
lemma fourFree : ∀ p p' l l' : Fin 4, p ≠ p' → l ≠ l' →
    E p l → E p l' → E p' l → ¬ E p' l' := by
  intro p p' l l'
  fin_cases p <;> fin_cases p' <;> fin_cases l <;> fin_cases l' <;> simp [E, Fin.ext_iff]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma mutations : ∀ (k : Fin 20) (m : Fin 3), ¬
    ((changed k.val (replacement k.val m)).eval (List.ofFn (witness k.val m)) = true ↔
      edgeOn (witness k.val m)) := by decide +kernel

lemma getOld {k : ℕ} {g : Gate} (h : C.gates[k]? = some g) : g = oldGate k := by
  simp [oldGate, List.getD_eq_getElem?_getD, h]

lemma getRange {k : ℕ} {g : Gate} (h : C.gates[k]? = some g) : k < 20 :=
  (List.getElem?_eq_some_iff.mp h).choose

lemma old_good : ∀ k : Fin 20,
    ((oldGate k.val).op = GateOp.and ∨ (oldGate k.val).op = GateOp.or) ∧
    (oldGate k.val).inputs = [left k.val, right k.val] ∧ left k.val ≠ right k.val ∧
    left k.val < 8 + k.val ∧ right k.val < 8 + k.val := by
  letI : DecidableEq GateOp := MetaComplexity.NestedCover.gateOpDecEq
  decide

lemma good (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < 8 + k ∧ v < 8 + k := by
  obtain rfl := getOld hg
  obtain ⟨ho, hi, hn, hu, hv⟩ := old_good ⟨k, getRange hg⟩
  exact ⟨ho, left k, right k, hi, hn, hu, hv⟩

lemma rigid (k u v : ℕ) (g g' : Gate) (hg : C.gates[k]? = some g) (hin : g.inputs = [u, v])
    (hg' : g' = ⟨.and, [u]⟩ ∨ g' = ⟨.and, [v]⟩ ∨
      (g.op = GateOp.and ∧ g' = ⟨.or, []⟩) ∨ (g.op = GateOp.or ∧ g' = ⟨.and, []⟩)) :
    ¬ ∀ x : Fin 8 → Bool, (changed k g').eval (List.ofFn x) = true ↔ edgeOn x := by
  have hk := getRange hg
  obtain rfl := getOld hg
  have hleft : u = left k := by simp [left, hin]
  have hright : v = right k := by simp [right, hin]
  have hcase (m : Fin 3) (hm : g' = replacement k m) :
      ¬ ∀ x : Fin 8 → Bool, (changed k g').eval (List.ofFn x) = true ↔ edgeOn x := by
    intro hall
    exact mutations ⟨k, hk⟩ m (by simpa only [hm] using hall (witness k m))
  rcases hg' with rfl | rfl | ⟨ho, rfl⟩ | ⟨ho, rfl⟩
  · exact hcase 0 (by simp [replacement, hleft])
  · exact hcase 1 (by simp [replacement, hright])
  · exact hcase 2 (by simp [replacement, ho, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide])
  · exact hcase 2 (by simp [replacement, ho, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide])

lemma no_single : ∀ i : Fin 8,
    (C.wires (List.ofFn (fun t : Fin 8 => decide (t = i)))).getD 10 false = false := by decide +kernel

lemma dirty : ∃ x : Fin 8 → Bool, (C.wires (List.ofFn x)).getD 10 false = true ∧ ¬edgeOn x := by
  refine ⟨bitInput 34, ?_⟩
  decide

lemma no_or_finite : ∀ k : Fin 20, (oldGate k.val).op = GateOp.or → 10 ∉ (oldGate k.val).inputs := by
  letI : DecidableEq GateOp := MetaComplexity.NestedCover.gateOpDecEq
  decide

lemma no_or (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g) (ho : g.op = GateOp.or) :
    10 ∉ g.inputs := by
  have hk := getRange hg
  obtain rfl := getOld hg
  exact no_or_finite ⟨k, hk⟩ ho

def readers : Set ℕ := {k | ∃ g : Gate, C.gates[k]? = some g ∧ 10 ∈ g.inputs}

def andReaders : Set ℕ := {k | ∃ g : Gate, C.gates[k]? = some g ∧ g.op = GateOp.and ∧ 10 ∈ g.inputs}

lemma readers_finite : readers.Finite := by
  refine (Set.finite_Iio (20 : ℕ)).subset ?_
  rintro k ⟨g, hg, _⟩
  exact getRange hg

lemma andReaders_subset : andReaders ⊆ readers := by
  rintro k ⟨g, hg, _, hw⟩
  exact ⟨g, hg, hw⟩

lemma andReaders_lower : 2 ≤ andReaders.ncard := by
  let A : Finset ℕ := {3, 4}
  have hsc : A.card = 2 := by decide
  have hsub : (A : Set ℕ) ⊆ andReaders := by
    intro k hk
    have h : k = 3 ∨ k = 4 := by simpa [A] using hk
    rcases h with rfl | rfl
    · exact ⟨⟨.and, [10, 0]⟩, rfl, rfl, by decide⟩
    · exact ⟨⟨.and, [10, 4]⟩, rfl, rfl, by decide⟩
  simpa only [Set.ncard_coe_finset, hsc] using
    (Set.ncard_le_ncard hsub (readers_finite.subset andReaders_subset))

lemma readers_lower : 2 ≤ readers.ncard :=
  andReaders_lower.trans (Set.ncard_le_ncard andReaders_subset readers_finite)

abbrev lost : Set (Fin 4 × Fin 4) :=
  {e | E e.1 e.2 ∧ C0.eval (List.ofFn (pairInput e.1 e.2)) = false}

lemma lost_lower : 3 ≤ lost.ncard := by
  let D : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 0), (0, 1)}
  have hdc : D.card = 3 := by decide
  have hsub : (D : Set (Fin 4 × Fin 4)) ⊆ lost := by
    intro e he
    have h : e = (0, 0) ∨ e = (1, 0) ∨ e = (0, 1) := by simpa [D] using he
    rcases h with rfl | rfl | rfl <;> decide +kernel
  simpa only [Set.ncard_coe_finset, hdc] using Set.ncard_mono hsub

lemma cover_lower (K : Finset (Fin 4 ⊕ Fin 4))
    (hK : ∀ (p l : Fin 4), E p l → C0.eval (List.ofFn (pairInput p l)) = false →
      Sum.inl p ∈ K ∨ Sum.inr l ∈ K) : 2 ≤ K.card := by
  have h1 := hK 0 1 (by decide +kernel) (by decide +kernel)
  have h2 := hK 1 0 (by decide +kernel) (by decide +kernel)
  apply Finset.one_lt_card.mpr
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    exact ⟨_, h1, _, h2, by decide⟩

def activeIndex : Finset ℕ :=
  {0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18}

def activeArc (y z : ℕ) : Prop :=
  ∃ (k : ℕ) (g : Gate), C0.gates[k]? = some g ∧ y ∈ g.inputs ∧ z = 8 + k ∧ ¬ Z z

def activeGate (k : ℕ) : Gate := C0.gates.getD k ⟨.or, []⟩

abbrev activeWire (i : ℕ) : Prop :=
  (C0.wires (List.ofFn fun _ : Fin 8 => true)).getD i false = true

lemma activeWire_notZ (i : ℕ) (h : activeWire i) : ¬ Z i := by
  intro hz
  exact Bool.false_ne_true ((hz (fun _ => true)).symm.trans h)

lemma activeGet (k : ℕ) (hk : k < C0.gates.length) :
    C0.gates[k]? = some (activeGate k) := by
  simp [activeGate, List.getD_eq_getElem?_getD, hk]

lemma activeStep (y k : ℕ) (hk : k < C0.gates.length)
    (hy : y ∈ (activeGate k).inputs) (hz : activeWire (8 + k)) :
    activeArc y (8 + k) :=
  ⟨k, activeGate k, activeGet k hk, hy, rfl, activeWire_notZ _ hz⟩

lemma activeIn (k : Fin 20) (hk : k.val ∈ activeIndex) :
    ∀ i ∈ (activeGate k.val).inputs, activeWire i := by
  have all : ∀ j : Fin 20, j.val ∈ activeIndex →
      ∀ i ∈ (activeGate j.val).inputs, activeWire i := by decide +kernel
  exact all k hk

lemma activePaths (k : ℕ) (hk : k ∈ activeIndex) :
    Relation.ReflTransGen activeArc (8 + k) C0.output := by
  have h26 : Relation.ReflTransGen activeArc 26 C0.output :=
    Relation.ReflTransGen.single (activeStep 26 19 (by decide) (by decide) (by decide))
  have h19 := (Relation.ReflTransGen.single (activeStep 19 18 (by decide) (by decide) (by decide))).trans h26
  have h25 := (Relation.ReflTransGen.single (activeStep 25 18 (by decide) (by decide) (by decide))).trans h26
  have h15 := (Relation.ReflTransGen.single (activeStep 15 11 (by decide) (by decide) (by decide))).trans h19
  have h18 := (Relation.ReflTransGen.single (activeStep 18 11 (by decide) (by decide) (by decide))).trans h19
  have h21 := (Relation.ReflTransGen.single (activeStep 21 17 (by decide) (by decide) (by decide))).trans h25
  have h24 := (Relation.ReflTransGen.single (activeStep 24 17 (by decide) (by decide) (by decide))).trans h25
  have h8 := (Relation.ReflTransGen.single (activeStep 8 7 (by decide) (by decide) (by decide))).trans h15
  have h14 := (Relation.ReflTransGen.single (activeStep 14 7 (by decide) (by decide) (by decide))).trans h15
  have h16 := (Relation.ReflTransGen.single (activeStep 16 10 (by decide) (by decide) (by decide))).trans h18
  have h17 := (Relation.ReflTransGen.single (activeStep 17 10 (by decide) (by decide) (by decide))).trans h18
  have h9 := (Relation.ReflTransGen.single (activeStep 9 13 (by decide) (by decide) (by decide))).trans h21
  have h20 := (Relation.ReflTransGen.single (activeStep 20 13 (by decide) (by decide) (by decide))).trans h21
  have h22 := (Relation.ReflTransGen.single (activeStep 22 16 (by decide) (by decide) (by decide))).trans h24
  have h23 := (Relation.ReflTransGen.single (activeStep 23 16 (by decide) (by decide) (by decide))).trans h24
  simp only [activeIndex, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h8
  · exact h9
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26

lemma activeCount :
    15 ≤ {k : ℕ | ∃ g : Gate, C0.gates[k]? = some g ∧ (∀ i ∈ g.inputs, ¬ Z i) ∧
      Relation.ReflTransGen activeArc (8 + k) C0.output}.ncard := by
  let A := {k : ℕ | ∃ g : Gate, C0.gates[k]? = some g ∧ (∀ i ∈ g.inputs, ¬ Z i) ∧
      Relation.ReflTransGen activeArc (8 + k) C0.output}
  have hcard : activeIndex.card = 15 := by decide
  have hlen : C0.gates.length = 20 := by rfl
  have hfinite : A.Finite := by
    apply (Set.finite_lt_nat C0.gates.length).subset
    intro k hk
    obtain ⟨g, hg, _⟩ := hk
    exact (List.getElem?_eq_some_iff.mp hg).choose
  have hinc : (activeIndex : Set ℕ) ⊆ A := by
    intro k hk
    change k ∈ activeIndex at hk
    have hlt : k < 20 := by
      simp only [activeIndex, Finset.mem_insert, Finset.mem_singleton] at hk
      omega
    refine ⟨activeGate k, activeGet k (hlen ▸ hlt), ?_, activePaths k hk⟩
    intro i hi
    exact activeWire_notZ i (activeIn ⟨k, hlt⟩ hk i hi)
  change 15 ≤ A.ncard
  simpa only [Set.ncard_coe_finset, hcard] using Set.ncard_le_ncard hinc hfinite

end PEqualNP.Outside.L_meta_3320_aux

open PEqualNP.Outside.L_meta_3320_aux PEqualNP.CircuitLowerBounds

set_option maxRecDepth 2048 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.L_meta_3320 :
  ¬ (∀ (a b : ℕ) (E : Fin a → Fin b → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ), (∀ (p p' : Fin a) (l l' : Fin b), p ≠ p' → l ≠ l' → E p l → E p l' → E p' l → ¬ E p' l') → (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ u v : ℕ, g.inputs = [u, v] ∧ u ≠ v ∧ u < a + b + k ∧ v < a + b + k) → C.output + 1 = a + b + C.size → (∀ x : Fin (a + b) → Bool, C.eval (List.ofFn x) = true ↔ ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) → (∀ (k u v : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → g.inputs = [u, v] → (g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u] } ∨ g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [v] } ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g' = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g' = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] })) → ¬ ∀ x : Fin (a + b) → Bool, (({ gates := C.gates.set k g', output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = true ↔ ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) → j < C.size → (∀ i : Fin (a + b), (C.wires (List.ofFn (fun t0 : Fin (a + b) => decide (t0 = i)))).getD (a + b + j) false = false) → (∃ x : Fin (a + b) → Bool, (C.wires (List.ofFn x)).getD (a + b + j) false = true ∧ ¬ ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) → 2 ≤ {k : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[k]? = some g ∧ a + b + j ∈ g.inputs}.ncard → (¬ ∃ (k k' w : ℕ) (g g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (g.inputs = [a + b + j, w] ∨ g.inputs = [w, a + b + j]) ∧ (∀ x : Fin (a + b) → Bool, (C.wires (List.ofFn x)).getD w false = true → ∃ (p : Fin a) (l : Fin b), E p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) ∧ C.gates[k']? = some g' ∧ g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ a + b + k ∈ g'.inputs) → ∀ C0 : PEqualNP.CircuitLowerBounds.Circuit, C0 = { gates := C.gates.map (fun h0 : PEqualNP.CircuitLowerBounds.Gate => ({ op := h0.op, inputs := h0.inputs.map (fun s0 : ℕ => if s0 = a + b + j then a + b + C.size else s0) } : PEqualNP.CircuitLowerBounds.Gate)), output := C.output } → ∀ Z : ℕ → Prop, (∀ i : ℕ, Z i ↔ ∀ x : Fin (a + b) → Bool, (C0.wires (List.ofFn x)).getD i false = false) → ∃ K : Finset (Fin a ⊕ Fin b), (∀ (p : Fin a) (l : Fin b), E p l → C0.eval (List.ofFn (fun t1 : Fin (a + b) => decide (t1 = Fin.castAdd b p) || decide (t1 = Fin.natAdd a l))) = false → Sum.inl p ∈ K ∨ Sum.inr l ∈ K) ∧ {k : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C0.gates[k]? = some g ∧ (∀ s1 ∈ g.inputs, ¬ Z s1) ∧ Relation.ReflTransGen (fun y z : ℕ => ∃ (k1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C0.gates[k1]? = some g1 ∧ y ∈ g1.inputs ∧ z = a + b + k1 ∧ ¬ Z z) (a + b + k) C0.output}.ncard + {e : Fin a × Fin b | E e.1 e.2 ∧ C0.eval (List.ofFn (fun t2 : Fin (a + b) => decide (t2 = Fin.castAdd b e.1) || decide (t2 = Fin.natAdd a e.2))) = false}.ncard + K.card + {k : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ a + b + j ∈ g.inputs}.ncard ≤ C.size + 1) := by
  intro hall
  have hns : ¬ ∃ (k k' w : ℕ) (g g' : Gate), C.gates[k]? = some g ∧ g.op = GateOp.or ∧
      (g.inputs = [10, w] ∨ g.inputs = [w, 10]) ∧
      (∀ x : Fin 8 → Bool, (C.wires (List.ofFn x)).getD w false = true → edgeOn x) ∧
      C.gates[k']? = some g' ∧ g'.op = GateOp.and ∧ 8 + k ∈ g'.inputs := by
    rintro ⟨k, _, w, g, _, hg, hop, hin, _⟩
    apply no_or k g hg hop
    rcases hin with h | h <;> rw [h] <;> simp
  obtain ⟨K, hK, hbudget⟩ := hall 4 4 E C 2 fourFree good (by decide) complete rigid
    (by decide) no_single dirty readers_lower hns C0 rfl Z (fun _ => Iff.rfl)
  have hcover : 2 ≤ K.card := cover_lower K hK
  have hlost := lost_lower
  have hread := andReaders_lower
  have hactive := activeCount
  change {k : ℕ | ∃ g : Gate, C0.gates[k]? = some g ∧ (∀ i ∈ g.inputs, ¬ Z i) ∧
      Relation.ReflTransGen activeArc (8 + k) C0.output}.ncard +
    lost.ncard + K.card + andReaders.ncard ≤ 21 at hbudget
  omega
