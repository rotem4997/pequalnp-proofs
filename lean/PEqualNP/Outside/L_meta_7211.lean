import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7211

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

theorem acts_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

theorem pre_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j o i : ℕ)
    (hj : j ≤ C.gates.length) (hi : i < n + j) :
    val (⟨C.gates.take j, o⟩ : Circuit) x i = val C x i := by
  unfold val
  simp only
  conv_rhs => rw [← List.take_append_drop j C.gates, wiresFrom_append]
  rw [prefix_val (C.gates.drop j) _ i (by simp [wiresFrom_length]; omega)]

theorem key (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (hand : g.op = GateOp.and) (a b : ℕ) (hin : g.inputs = [a, b]) (ha : a < b)
    (hb : b < n + j) (x : Fin n → Bool) :
    val C x (n + j) = (val (⟨C.gates.take j, 0⟩ : Circuit) x a &&
      val (⟨C.gates.take j, 0⟩ : Circuit) x b) := by
  have hjl : j ≤ C.gates.length := (List.getElem?_eq_some_iff.1 hg).1.le
  rw [val_gate C x hg, hin, hand, pre_val C x j 0 a hjl (by omega),
    pre_val C x j 0 b hjl hb]
  have ha' : a < n + j := by omega
  simp [GateOp.eval, operand, ha', hb]

end PEqualNP.Outside.L_meta_7211

open PEqualNP.Outside.L_meta_7211 in
theorem PEqualNP.Outside.L_meta_7211 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     x1 ≤ x2.output →       x2.output < x1 + x2.size →         (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x2.output - x1]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and) →           (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x7]? = Option.some x8 → ∃ (x10 : ℕ) (x11 : ℕ), x8.inputs = [x10, x11] ∧ x10 < x11 ∧ x11 < x1 + x7) →             ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ),               PEqualNP.MetaComplexity.Monotone2 x8 ∧                 x8.size + (1 : ℕ) ≤ x2.size ∧                   x9 < x10 ∧                     x10 < x1 + x8.size ∧                       have x11 : ℕ → (Fin x1 → Bool) → Bool := fun (x11 : ℕ) (x12 : Fin x1 → Bool) => (x8.wires (List.ofFn x12)).getD x11 Bool.false;                       (∀ (x12 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x12 = Bool.true → x11 x9 x12 = Bool.true ∧ x11 x10 x12 = Bool.true) ∧ ∀ (x12 x13 : Fin x1 → Bool), x11 x9 x12 = Bool.true → x11 x10 x13 = Bool.true → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x16 : Fin x1) => x12 x16 || x13 x16) = Bool.true := by
  intro x1 C hC hle hlt hex hshape
  obtain ⟨g, hg, hand⟩ := hex
  obtain ⟨a, b, hin, hab, hb⟩ := hshape _ g hg
  have hjlen : C.output - x1 < C.gates.length := (List.getElem?_eq_some_iff.1 hg).1
  have hout : C.output = x1 + (C.output - x1) := by omega
  have hC' : PEqualNP.MetaComplexity.Monotone2
      (⟨C.gates.take (C.output - x1), 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) :=
    fun g' hg' => hC g' (List.mem_of_mem_take hg')
  have hcf : ∀ x : Fin x1 → Bool, PEqualNP.MetaComplexity.circuitFun x1 C x =
      (val (⟨C.gates.take (C.output - x1), 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x a &&
       val (⟨C.gates.take (C.output - x1), 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) x b) := by
    intro x
    show val C x C.output = _
    have hk := key x1 C _ g hg hand a b hin hab hb x
    rw [← hout] at hk
    exact hk
  refine ⟨⟨C.gates.take (C.output - x1), 0⟩, a, b, hC', ?_, hab, ?_, ?_⟩
  · show (C.gates.take (C.output - x1)).length + 1 ≤ C.gates.length
    simp only [List.length_take]
    omega
  · show b < x1 + (C.gates.take (C.output - x1)).length
    simp only [List.length_take]
    omega
  · dsimp only
    refine ⟨fun x h => ?_, fun x y h1 h2 => ?_⟩
    · rw [hcf] at h
      exact Bool.and_eq_true_iff.1 h
    · rw [hcf]
      have m1 := acts_mono hC' (x := x) (y := fun i => x i || y i)
        (by intro i hi; simp [hi])
      have m2 := acts_mono hC' (x := y) (y := fun i => x i || y i)
        (by intro i hi; simp [hi])
      exact Bool.and_eq_true_iff.2 ⟨m1 a h1, m2 b h2⟩
