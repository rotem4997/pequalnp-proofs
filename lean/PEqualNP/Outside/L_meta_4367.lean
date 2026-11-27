import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4367

def target (x : Fin 9 → Bool) : Bool :=
  ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
    x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

def seed (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 3]

def exceptions (op : GateOp) : List ℕ :=
  if op.eval [] = true then [3, 9, 30, 39, 49] else [2, 4, 8, 31, 34, 35]

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [value g ws]) w

lemma common_suffix (gs : List Gate) (u v : List Bool)
    (agree : ∀ g ∈ gs, ∀ s, value g (u ++ s) = value g (v ++ s)) (s : List Bool) :
    ∃ t, run gs (u ++ s) = u ++ t ∧ run gs (v ++ s) = v ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨s, rfl, rfl⟩
  | cons g gs ih =>
    have h := agree g List.mem_cons_self s
    obtain ⟨t, hu, hv⟩ := ih (fun k hk => agree k (List.mem_cons_of_mem _ hk))
      (s ++ [value g (u ++ s)])
    exact ⟨t, by simpa only [run, List.foldl_cons, List.append_assoc] using hu,
      by simpa only [run, List.foldl_cons, List.append_assoc, h] using hv⟩

lemma seed_value (g : Gate) (raw : ∀ i ∈ g.inputs, i < 10) (x : Fin 9 → Bool) (s : List Bool) :
    value g (seed x ++ s) = value g (seed x) := by
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i hi
  exact List.getD_append _ _ _ _ (by simpa [seed] using raw i hi)

lemma count_split (C : Circuit) (g : Gate) (p q : List Gate) (he : C.gates = p ++ g :: q) (i : ℕ) :
    (C.output :: C.gates.flatMap Gate.inputs).count i =
    (C.output :: (p ++ q).flatMap Gate.inputs).count i + g.inputs.count i := by
  rw [he]
  simp only [List.flatMap_append, List.flatMap_cons, List.count_cons, List.count_append]
  omega

lemma force_read (C : Circuit) (correct : ∀ x, C.eval (seed x) = target x)
    (g : Gate) (hg : g ∈ C.gates) (raw : ∀ i ∈ g.inputs, i < 10)
    (D : ℕ → Prop) (ports : ∀ i, D i → i ∈ g.inputs)
    (x y : Fin 9 → Bool) (diff : target x ≠ target y)
    (agree : ∀ j : Fin 10, ¬ D j.val → (seed x).getD j.val false = (seed y).getD j.val false)
    (masked : value g (seed x) = value g (seed y)) :
    ∃ i, D i ∧ 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count i := by
  classical
  by_contra no
  obtain ⟨p, q, he⟩ := List.append_of_mem hg
  have unused (i : ℕ) (hi : D i) : i ∉ C.output :: (p ++ q).flatMap Gate.inputs := by
    intro used
    have h₁ := List.count_pos_iff.mpr used
    have h₂ := List.count_pos_iff.mpr (ports i hi)
    have h₃ := count_split C g p q he i
    exact no ⟨i, hi, by omega⟩
  have bit_agree (s : List Bool) (i : ℕ) (hi : ¬ D i) :
      (seed x ++ s).getD i false = (seed y ++ s).getD i false := by
    by_cases h : i < 10
    · rw [List.getD_append _ _ _ _ (by simpa [seed] using h),
          List.getD_append _ _ _ _ (by simpa [seed] using h)]
      exact agree ⟨i, h⟩ hi
    · rw [List.getD_append_right _ _ _ _ (by simp [seed]; omega),
          List.getD_append_right _ _ _ _ (by simp [seed]; omega)]
      simp [seed]
  have gates_agree (k : Gate) (hk : k ∈ C.gates) (s : List Bool) :
      value k (seed x ++ s) = value k (seed y ++ s) := by
    by_cases e : k = g
    · subst k
      simpa only [seed_value g raw] using masked
    · have hk' : k ∈ p ++ q := by
        simp only [he, List.mem_append, List.mem_cons] at hk
        exact List.mem_append.mpr (hk.imp_right (fun h => h.resolve_left e))
      apply congrArg k.op.eval
      apply List.map_congr_left
      intro i hki
      apply bit_agree
      exact fun hi => unused i hi (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨k, hk', hki⟩))
  obtain ⟨t, hu, hv⟩ := common_suffix C.gates (seed x) (seed y) gates_agree []
  simp only [List.append_nil] at hu hv
  apply diff
  rw [← correct, ← correct]
  change (run C.gates (seed x)).getD C.output false = (run C.gates (seed y)).getD C.output false
  rw [hu, hv]
  exact bit_agree t _ (fun hi => unused _ hi List.mem_cons_self)

def binary (t : Bool) : GateOp := if t then .and else .or

def bits (n : ℕ) (j : Fin 9) : Bool := n.testBit j.val

-- Rows select the first port, columns the second. Set bit a to get the other assignment.
def lowMask (t : Bool) (a : Fin 9) (b : Fin 10) : ℕ :=
  let rows : List (List ℕ) := if t then
    [[0, 40, 10, 0, 10, 10, 10, 10, 10, 0],
     [4, 0, 1, 1, 1, 1, 1, 1, 1, 4],
     [2, 8, 0, 2, 2, 2, 2, 2, 2, 2],
     [0, 5, 257, 0, 5, 5, 5, 5, 5, 0],
     [8, 1, 1, 1, 0, 1, 1, 1, 1, 0],
     [128, 1, 1, 1, 1, 0, 1, 1, 1, 128],
     [2, 256, 2, 2, 2, 2, 0, 2, 2, 2],
     [4, 4, 32, 4, 4, 4, 4, 0, 4, 4],
     [8, 8, 8, 32, 8, 8, 8, 8, 0, 32]]
  else
    [[0, 10, 0, 10, 0, 40, 104, 138, 0, 10],
     [1, 0, 4, 9, 20, 36, 64, 129, 257, 1],
     [9, 2, 0, 8, 18, 34, 72, 128, 258, 8],
     [5, 0, 5, 0, 0, 0, 69, 385, 257, 5],
     [1, 10, 5, 8, 0, 40, 65, 129, 257, 1],
     [1, 130, 5, 9, 144, 0, 65, 128, 256, 1],
     [257, 2, 260, 10, 18, 34, 0, 130, 256, 10],
     [5, 34, 4, 40, 20, 32, 68, 0, 260, 5],
     [9, 10, 36, 8, 48, 32, 64, 136, 0, 8]]
  (rows.getD a.val []).getD b.val 0

def low (t : Bool) (a : Fin 9) (b : Fin 10) := bits (lowMask t a b)

def high (t : Bool) (a : Fin 9) (b : Fin 10) (j : Fin 9) :=
  (j == a) || low t a b j

set_option maxHeartbeats 2000000 in
lemma witnesses (t : Bool) (a : Fin 9) :
    ∀ b : Fin 10, a.val ≠ b.val → 10 * a.val + b.val ∉ exceptions (binary t) →
    let x := low t a b
    let y := high t a b
    target x ≠ target y ∧
      (∀ j : Fin 10, j.val ≠ a.val → (seed x).getD j.val false = (seed y).getD j.val false) ∧
      value ⟨binary t, [a.val, b.val]⟩ (seed x) = value ⟨binary t, [a.val, b.val]⟩ (seed y) := by
  cases t <;> fin_cases a <;> decide

lemma swap_value (t : Bool) (a b : ℕ) (w : List Bool) :
    value ⟨binary t, [b,a]⟩ w = value ⟨binary t, [a,b]⟩ w := by
  cases t <;> simp [value, binary, GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma binary_masked (g : Gate) (t : Bool) (a b : ℕ)
    (op : g.op = binary t) (order : g.inputs = [a,b] ∨ g.inputs = [b,a])
    (u v : List Bool)
    (masked : value ⟨binary t, [a,b]⟩ u = value ⟨binary t, [a,b]⟩ v) :
    value g u = value g v := by
  obtain ⟨o, ins⟩ := g
  change o = binary t at op
  change ins = [a,b] ∨ ins = [b,a] at order
  subst o
  rcases order with rfl | rfl
  · exact masked
  · simpa only [swap_value t a b] using masked

lemma bound_ports (g : Gate) (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (order : g.inputs = [a,b] ∨ g.inputs = [b,a]) : ∀ i ∈ g.inputs, i < 10 := by
  intro i h
  rcases order with e | e <;> rw [e] at h <;> simp only [List.mem_cons, List.not_mem_nil,
    or_false] at h <;> rcases h with rfl | rfl <;> assumption

lemma single_port (C : Circuit) (correct : ∀ x, C.eval (seed x) = target x)
    (g : Gate) (hg : g ∈ C.gates) (a : Fin 9) (b : Fin 10) (t : Bool)
    (order : g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val])
    (op : g.op = binary t) (outside : 10 * a.val + b.val ∉ exceptions (binary t)) :
    2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count a.val := by
  by_cases eq : a.val = b.val
  · have ports : g.inputs = [a.val,a.val] := by simpa only [← eq, or_self] using order
    obtain ⟨p, q, he⟩ := List.append_of_mem hg
    rw [count_split C g p q he, ports]
    simp
  · obtain ⟨diff, agree, masked⟩ := witnesses t a b eq outside
    have occurs : a.val ∈ g.inputs := by rcases order with e | e <;> simp [e]
    obtain ⟨i, rfl, h⟩ := force_read C correct g hg
      (bound_ports g a.val b.val (by omega) b.isLt order) (fun i => i = a.val)
      (fun i hi => hi ▸ occurs) _ _ diff agree
      (binary_masked g t _ _ op order _ _ masked)
    exact h

lemma pair_ports (C : Circuit) (correct : ∀ x, C.eval (seed x) = target x)
    (g : Gate) (hg : g ∈ C.gates) (op : g.op = GateOp.and)
    (order : g.inputs = [0,3] ∨ g.inputs = [3,0]) :
    2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 0 ∨
    2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 3 := by
  have occurs : ∀ i : ℕ, i = 0 ∨ i = 3 → i ∈ g.inputs := by
    intro i h
    rcases h with rfl | rfl <;> rcases order with e | e <;> simp [e]
-- These assignments hold wire 1 high and exchange the values of wires 0 and 3.
  obtain ⟨i, hi, count⟩ := force_read C correct g hg
    (bound_ports g 0 3 (by decide) (by decide) order) (fun i => i = 0 ∨ i = 3)
    occurs (bits 3) (bits 10) (by decide) (by decide)
    (binary_masked g true 0 3 op order _ _ (by decide))
  rcases hi with rfl | rfl
  · exact Or.inl count
  · exact Or.inr count

end PEqualNP.Outside.L_meta_4367

open PEqualNP.Outside.L_meta_4367

theorem PEqualNP.Outside.L_meta_4367 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.GateOp → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.GateOp) => if x3.eval [] = Bool.true then [(3 : ℕ), (9 : ℕ), (30 : ℕ), (39 : ℕ), (49 : ℕ)] else [(2 : ℕ), (4 : ℕ), (8 : ℕ), (31 : ℕ), (34 : ℕ), (35 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (x2 x5) = x1 x5) → (∀ x6 ∈ x4.gates, ∀ (x8 : Fin (9 : ℕ)) (x9 : Fin (10 : ℕ)), x6.inputs = [↑x8, ↑x9] ∨ x6.inputs = [↑x9, ↑x8] → x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) * ↑x8 + ↑x9 ∉ x3 x6.op → (2 : ℕ) ≤ List.count (↑x8) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) ∧ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates ∨ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(3 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates → (2 : ℕ) ≤ List.count (0 : ℕ) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∨ (2 : ℕ) ≤ List.count (3 : ℕ) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) := by
  intro f enc exc C correct
  constructor
  · intro g hg a b order op outside
    change 10 * a.val + b.val ∉ exceptions g.op at outside
    rcases op with h | h
    · rw [h] at outside
      exact single_port C correct g hg a b true order h outside
    · rw [h] at outside
      exact single_port C correct g hg a b false order h outside
  · intro present
    rcases present with hg | hg
    · exact pair_ports C correct _ hg rfl (Or.inl rfl)
    · exact pair_ports C correct _ hg rfl (Or.inr rfl)
