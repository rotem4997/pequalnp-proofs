import Mathlib
import PEqualNP.Defs

-- The wire monotonicity proof uses the same fold argument as the replacement rewrite.
namespace PEqualNP.Outside.L_meta_2792

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

private def implication (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

private theorem run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem append_imp {a b : List Bool} {u v : Bool} (len : a.length = b.length)
    (before : implication a b) (last : u = true → v = true) :
    implication (a ++ [u]) (b ++ [v]) := by
  intro i old
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi] at old
    rw [List.getD_append _ _ _ _ (len ▸ hi)]
    exact before i old
  · rw [List.getD_append_right _ _ _ _ (by omega)] at old
    rw [List.getD_append_right _ _ _ _ (by omega), ← len]
    cases offset : i - a.length with
    | zero => exact last (by simpa [offset] using old)
    | succ k => simp [offset] at old

private theorem op_imp {op : GateOp} (ao : op = GateOp.and ∨ op = GateOp.or)
    (pins : List ℕ) {a b : ℕ → Bool} (rows : ∀ i ∈ pins, a i = true → b i = true) :
    op.eval (pins.map a) = true → op.eval (pins.map b) = true := by
  rcases ao with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro old _ hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact rows i hi (old _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, old⟩
    exact ⟨b i, ⟨i, hi, rfl⟩, rows i hi old⟩

private theorem run_imp (gs : List Gate)
    (ao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : List Bool} (len : a.length = b.length) (entries : implication a b) :
    implication (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact entries
  | cons g gs ih =>
    change implication (run gs (step a g)) (run gs (step b g))
    apply ih (fun t ht => ao t (List.mem_cons_of_mem _ ht)) (by simp [step, len])
    apply append_imp len entries
    exact op_imp (ao g List.mem_cons_self) g.inputs (fun i _ => entries i)

private theorem run_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (earlier : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (run gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at earlier ⊢
      change (run gs (step w g)).getD w.length false = _
      rw [run_keeps _ _ _ (by simp [step]), step, List.getD_append_right _ _ _ _ (Nat.le_refl _),
        Nat.sub_self]
      change g.op.eval (g.inputs.map fun i => w.getD i false) = _
      congr 1
      apply List.map_congr_left
      intro i hi
      exact (run_keeps _ _ _ (earlier i hi)).symm
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have len : (step w g).length + j = w.length + (j + 1) := by simp [step]; omega
      have earlier' : ∀ i ∈ gs[j].inputs, i < (step w g).length + j := by
        simpa only [List.getElem_cons_succ, len] using earlier
      change (run gs (step w g)).getD (w.length + (j + 1)) false = _
      rw [← len]
      exact ih (step w g) j hj' earlier'

private def wire {n : ℕ} (C : Circuit) (i : ℕ) (p l : Fin n → Bool) : Bool :=
  (run C.gates (List.ofFn p ++ List.ofFn l)).getD i false

private def trueRows {n : ℕ} (C : Circuit) (i : ℕ) : Set ((Fin n → Bool) × (Fin n → Bool)) :=
  {a | wire C i a.1 a.2 = true}

private theorem raw_wire {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private theorem inputs_imp {n : ℕ} {p l p' l' : Fin n → Bool}
    (points : ∀ i, p i = true → p' i = true) (lines : ∀ i, l i = true → l' i = true) :
    implication (List.ofFn p ++ List.ofFn l) (List.ofFn p' ++ List.ofFn l') := by
  intro i old
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using hi), raw_wire _ ⟨i, hi⟩] at old
    rw [List.getD_append _ _ _ _ (by simpa using hi), raw_wire _ ⟨i, hi⟩]
    exact points _ old
  · have hp : (List.ofFn p).length ≤ i := by simpa using Nat.le_of_not_gt hi
    have hp' : (List.ofFn p').length ≤ i := by simpa using Nat.le_of_not_gt hi
    rw [List.getD_append_right _ _ _ _ hp, List.length_ofFn] at old
    rw [List.getD_append_right _ _ _ _ hp', List.length_ofFn]
    by_cases hj : i - n < n
    · rw [raw_wire _ ⟨i - n, hj⟩] at old ⊢
      exact lines _ old
    · have ho : (List.ofFn l).length ≤ i - n := by simpa using Nat.le_of_not_gt hj
      rw [List.getD_eq_default _ _ ho] at old
      cases old

private theorem wire_imp {n : ℕ} (C : Circuit) (ao : Monotone2 C) (i : ℕ)
    {p l p' l' : Fin n → Bool} (points : ∀ j, p j = true → p' j = true)
    (lines : ∀ j, l j = true → l' j = true) : wire C i p l = true → wire C i p' l' = true :=
  run_imp _ (fun g hg => by simpa using (ao g hg).1) (by simp) (inputs_imp points lines) i

private theorem wire_left {n : ℕ} (C : Circuit) (ao : Monotone2 C) (i : ℕ)
    (flat : ∀ p : Fin n → Bool, wire C i p (fun _ => false) = wire C i p (fun _ => true))
    (p l : Fin n → Bool) : wire C i p l = wire C i p (fun _ => false) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [flat p]
    exact wire_imp C ao i (fun _ h => h) (fun _ _ => rfl) h
  · intro h
    exact wire_imp C ao i (fun _ h => h) (fun _ h => by cases h) h

private theorem wire_right {n : ℕ} (C : Circuit) (ao : Monotone2 C) (i : ℕ)
    (flat : ∀ l : Fin n → Bool, wire C i (fun _ => false) l = wire C i (fun _ => true) l)
    (p l : Fin n → Bool) : wire C i p l = wire C i (fun _ => false) l := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [flat l]
    exact wire_imp C ao i (fun _ _ => rfl) (fun _ h => h) h
  · intro h
    exact wire_imp C ao i (fun _ h => by cases h) (fun _ h => h) h

private theorem left_product {n : ℕ} (C : Circuit) (ao : Monotone2 C) (i : ℕ)
    (flat : ∀ p : Fin n → Bool, wire C i p (fun _ => false) = wire C i p (fun _ => true)) :
    trueRows (n := n) C i = {p | wire C i p (fun _ => false) = true} ×ˢ Set.univ := by
  ext a
  simp [trueRows, wire_left C ao i flat a.1 a.2]

private theorem right_product {n : ℕ} (C : Circuit) (ao : Monotone2 C) (i : ℕ)
    (flat : ∀ l : Fin n → Bool, wire C i (fun _ => false) l = wire C i (fun _ => true) l) :
    trueRows (n := n) C i = Set.univ ×ˢ {l | wire C i (fun _ => false) l = true} := by
  ext a
  simp [trueRows, wire_right C ao i flat a.1 a.2]

private theorem both_flat {n : ℕ} (C : Circuit) (ao : Monotone2 C) (i : ℕ)
    (left : ∀ p : Fin n → Bool, wire C i p (fun _ => false) = wire C i p (fun _ => true))
    (right : ∀ l : Fin n → Bool, wire C i (fun _ => false) l = wire C i (fun _ => true) l) :
    trueRows (n := n) C i = Set.univ ∨ trueRows (n := n) C i = ∅ := by
  have fixed (p l : Fin n → Bool) : wire C i p l = wire C i (fun _ => false) (fun _ => false) :=
    (wire_left C ao i left p l).trans (wire_right C ao i right p (fun _ => false))
  cases h : wire C i (fun _ : Fin n => false) (fun _ => false)
  · right
    ext a
    simp [trueRows, fixed a.1 a.2, h]
  · left
    ext a
    simp [trueRows, fixed a.1 a.2, h]

private def pointOnly {n : ℕ} (C : Circuit) (i : ℕ) : Prop :=
  ∀ p : Fin n → Bool, wire C i p (fun _ => false) = wire C i p (fun _ => true)

private def lineOnly {n : ℕ} (C : Circuit) (i : ℕ) : Prop :=
  ∀ l : Fin n → Bool, wire C i (fun _ => false) l = wire C i (fun _ => true) l

private theorem choose_pin (P : ℕ → Prop) (a b : ℕ) (h : ¬ ∀ i ∈ [a,b], ¬ P i) : P a ∨ P b := by
  classical
  by_contra! hn
  apply h
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact hn.1
  · exact hn.2

end PEqualNP.Outside.L_meta_2792


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2792

theorem PEqualNP.Outside.L_meta_2792 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 → ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 < x9 ∧ x9 < x1 + x1 + x5) →       (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x6]? = Option.some x7 → x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 ∉ x3 → ¬((∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.false)).getD x11 Bool.false ≠ (x2.wires (List.ofFn x13 ++ List.replicate x1 Bool.true)).getD x11 Bool.false) ∨ ∀ x11 ∈ x7.inputs, ∃ (x13 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x13)).getD x11 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x13)).getD x11 Bool.false)) →         ∃ (x7 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),           (∀ (x8 : Fin x1), x7 ↑x8 = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.1 x8 = Bool.true} ∧ x7 (x1 + ↑x8) = {x9 : (Fin x1 → Bool) × (Fin x1 → Bool) | x9.2 x8 = Bool.true}) ∧             (∀ x8 < x2.size,                 ∃ x10 < x1 + x1 + x8,                   ∃ x11 < x1 + x1 + x8,                     have x12 : Set ((Fin x1 → Bool) × (Fin x1 → Bool)) := x7 (x1 + x1 + x8);                     x12 = x7 x10 ∪ x7 x11 ∨ x12 = x7 x10 ∨ x12 = ∅ ∨ x12 = x7 x10 ∩ x7 x11 ∧ (x8 ∈ x3 ∨ ∃ (x13 : Set (Fin x1 → Bool)) (x14 : Set (Fin x1 → Bool)), x7 x10 = x13 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x14)) ∧               ∀ (x8 x9 : Fin x1 → Bool), (x8, x9) ∈ x7 x2.output ↔ PEqualNP.MetaComplexity.circuitFun (x1 + x1) x2 (Fin.append x8 x9) = Bool.true := by
  classical
  intro n C cross ao pins noCross
  refine ⟨trueRows (n := n) C, ?_, ?_, ?_⟩
  · intro i
    constructor <;> ext x
    · change (run C.gates (List.ofFn x.1 ++ List.ofFn x.2)).getD i.val false = true ↔ x.1 i = true
      have hi : i.val < (List.ofFn x.1).length := by simp
      rw [run_keeps _ _ _ (by simp; omega), List.getD_append _ _ _ _ hi, raw_wire]
    · change (run C.gates (List.ofFn x.1 ++ List.ofFn x.2)).getD (n + i.val) false = true ↔ x.2 i = true
      have hi : (List.ofFn x.1).length ≤ n + i.val := by simp
      rw [run_keeps _ _ _ (by simp), List.getD_append_right _ _ _ _ hi, List.length_ofFn,
        Nat.add_sub_cancel_left, raw_wire]
  · intro j hj
    change j < C.gates.length at hj
    let g := C.gates[j]
    have entry : C.gates[j]? = some g := List.getElem?_eq_getElem hj
    obtain ⟨a, b, hab, ab, bj⟩ := pins j g entry
    have aj : a < n + n + j := ab.trans bj
    have evalAt (p l : Fin n → Bool) :
        wire C (n + n + j) p l = g.op.eval [wire C a p l, wire C b p l] := by
      have len : (List.ofFn p ++ List.ofFn l).length = n + n := by simp
      unfold wire
      rw [← len, run_gate C.gates _ j hj]
      · change g.op.eval (g.inputs.map _) = _
        rw [hab]
        rfl
      · change ∀ i ∈ g.inputs, i < _
        rw [hab, len]
        simp [aj, bj]
    have hops : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using (ao g (List.getElem_mem hj)).1
    rcases hops with ha | ho
    · have inter : trueRows (n := n) C (n + n + j) = trueRows C a ∩ trueRows C b := by
        ext x
        simp [trueRows, evalAt x.1 x.2, ha, GateOp.eval]
      by_cases allowed : j ∈ cross
      · exact ⟨a, aj, b, bj, Or.inr (Or.inr (Or.inr ⟨inter, Or.inl allowed⟩))⟩
      have clean := noCross j g entry ha allowed
      have pointPin : pointOnly (n := n) C a ∨ pointOnly (n := n) C b := by
        apply choose_pin
        intro all
        apply clean
        left
        rw [hab]
        intro i hi
        rw [← List.ofFn_const n false, ← List.ofFn_const n true]
        exact not_forall.mp (all i hi)
      have linePin : lineOnly (n := n) C a ∨ lineOnly (n := n) C b := by
        apply choose_pin
        intro all
        apply clean
        right
        rw [hab]
        intro i hi
        rw [← List.ofFn_const n false, ← List.ofFn_const n true]
        exact not_forall.mp (all i hi)
      rcases pointPin with pa | pb <;> rcases linePin with la | lb
      · rcases both_flat C ao a pa la with emptyOrFull | empty
        · exact ⟨b, bj, a, aj, Or.inr (Or.inl (by simpa only [emptyOrFull, Set.univ_inter] using inter))⟩
        · exact ⟨a, aj, b, bj, Or.inr (Or.inr (Or.inl (by simpa only [empty, Set.empty_inter] using inter)))⟩
      · refine ⟨a, aj, b, bj, Or.inr (Or.inr (Or.inr ⟨inter, Or.inr ?_⟩))⟩
        exact ⟨_, _, left_product C ao a pa, right_product C ao b lb⟩
      · refine ⟨b, bj, a, aj, Or.inr (Or.inr (Or.inr ⟨inter.trans (Set.inter_comm _ _), Or.inr ?_⟩))⟩
        exact ⟨_, _, left_product C ao b pb, right_product C ao a la⟩
      · rcases both_flat C ao b pb lb with emptyOrFull | empty
        · exact ⟨a, aj, b, bj, Or.inr (Or.inl (by simpa only [emptyOrFull, Set.inter_univ] using inter))⟩
        · exact ⟨a, aj, b, bj, Or.inr (Or.inr (Or.inl (by simpa only [empty, Set.inter_empty] using inter)))⟩
    · refine ⟨a, aj, b, bj, Or.inl ?_⟩
      ext x
      simp [trueRows, evalAt x.1 x.2, ho, GateOp.eval]
  · intro p l
    change (run C.gates (List.ofFn p ++ List.ofFn l)).getD C.output false = true ↔
      (run C.gates (List.ofFn (Fin.append p l))).getD C.output false = true
    rw [List.ofFn_fin_append]
