import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5028_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The evaluation lemmas are adapted from the checked proof of L-meta-1485.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem or_wire (n : ℕ) (C : Circuit) (back : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = .or)
    (x : Fin n → Bool) :
    wireValue C (List.ofFn x) (n + j) = true ↔
      ∃ i ∈ (gateAt C j).inputs, wireValue C (List.ofFn x) i = true := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have step := foldl_getD_gate C.gates (List.ofFn x) j hj
  rw [hlen, ← gateAt_eq hj, hor] at step
  change wireValue C (List.ofFn x) (n + j) = GateOp.or.eval
    ((gateAt C j).inputs.map fun i => if i < n + j then wireValue C (List.ofFn x) i else false) at step
  have hmap :
      ((gateAt C j).inputs.map fun i => if i < n + j then wireValue C (List.ofFn x) i else false) =
      (gateAt C j).inputs.map (wireValue C (List.ofFn x)) := by
    apply List.map_congr_left
    intro i hi
    exact ite_eq_left (back j hj i hi)
  rw [step, hmap]
  simp [GateOp.eval, List.any_eq_true]

theorem union_support {α : Type} (admissible : ℕ → Prop) (on : α → ℕ → Prop)
    (W : List ℕ)
    (sources : ∀ w ∈ W, ∃ S : Finset ℕ, (∀ i ∈ S, admissible i) ∧
      ∀ x, on x w ↔ ∃ i ∈ S, on x i) :
    ∃ S : Finset ℕ, (∀ i ∈ S, admissible i) ∧
      ∀ x, (∃ w ∈ W, on x w) ↔ ∃ i ∈ S, on x i := by
  induction W with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons w rest ih =>
    obtain ⟨A, hA, ea⟩ := sources w (by simp)
    obtain ⟨B, hB, eb⟩ := ih (fun i hi => sources i (by simp [hi]))
    refine ⟨A ∪ B, ?_, ?_⟩
    · intro i hi
      exact (Finset.mem_union.mp hi).elim (hA i) (hB i)
    · intro x
      constructor
      · rintro ⟨i, hi, hx⟩
        rcases List.mem_cons.mp hi with rfl | hi
        · obtain ⟨k, hk, ht⟩ := (ea x).mp hx
          exact ⟨k, Finset.mem_union_left _ hk, ht⟩
        · obtain ⟨k, hk, ht⟩ := (eb x).mp ⟨i, hi, hx⟩
          exact ⟨k, Finset.mem_union_right _ hk, ht⟩
      · rintro ⟨k, hk, hx⟩
        rcases Finset.mem_union.mp hk with hk | hk
        · exact ⟨w, List.mem_cons_self, (ea x).mpr ⟨k, hk, hx⟩⟩
        · obtain ⟨i, hi, ht⟩ := (eb x).mpr ⟨k, hk, hx⟩
          exact ⟨i, List.mem_cons_of_mem _ hi, ht⟩

theorem support_at_wire (n : ℕ) (C : Circuit) (mono : Monotone2 C) (back : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.size) :
    ∃ S : Finset ℕ, (∀ i ∈ S, i ≤ w ∧ (i < n ∨ (gateAt C (i - n)).op = .and)) ∧
      ∀ x : Fin n → Bool, wireValue C (List.ofFn x) w = true ↔
        ∃ i ∈ S, wireValue C (List.ofFn x) i = true := by
  induction w using Nat.strongRecOn with
  | ind w ih =>
    by_cases hraw : w < n
    · exact ⟨{w}, by simp [hraw], by simp⟩
    let j := w - n
    have hj : j < C.gates.length := by
      change w < n + C.gates.length at hw
      omega
    have he : n + j = w := by omega
    have hm : (gateAt C j).op = .and ∨ (gateAt C j).op = .or := by
      simpa using (mono _ (by rw [gateAt_eq hj]; exact List.getElem_mem hj)).1
    rcases hm with hand | hor
    · have hjw : w - n = j := rfl
      exact ⟨{w}, by simp [hjw, hand], by simp⟩
    have hchild (i : ℕ) (hi : i ∈ (gateAt C j).inputs) : i < w := by
      simpa only [he] using back j hj i hi
    have sources (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
        ∃ S : Finset ℕ, (∀ u ∈ S, u ≤ w ∧ (u < n ∨ (gateAt C (u - n)).op = .and)) ∧
          ∀ x : Fin n → Bool, wireValue C (List.ofFn x) i = true ↔
            ∃ u ∈ S, wireValue C (List.ofFn x) u = true := by
      have hlt := hchild i hi
      obtain ⟨S, hs, es⟩ := ih i hlt (by omega)
      refine ⟨S, ?_, es⟩
      intro u hu
      exact ⟨(hs u hu).1.trans hlt.le, (hs u hu).2⟩
    obtain ⟨S, hs, es⟩ := union_support
      (fun u => u ≤ w ∧ (u < n ∨ (gateAt C (u - n)).op = .and))
      (fun (x : Fin n → Bool) i => wireValue C (List.ofFn x) i = true)
      (gateAt C j).inputs sources
    refine ⟨S, hs, fun x => ?_⟩
    exact (he ▸ or_wire n C back j hj hor x).trans (es x)

end PEqualNP.Outside.L_meta_5028_aux

theorem PEqualNP.Outside.L_meta_5028 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x8 : Finset ℕ), (∀ x9 ∈ x8, x9 < x2.output ∧ (x9 < x1 ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x9 - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.and)) ∧ ∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x9) x10 = Bool.true := by
  intro n C mono back lo hi hor
  obtain ⟨S, hs, es⟩ := PEqualNP.Outside.L_meta_5028_aux.support_at_wire n C mono back C.output hi
  refine ⟨S, ?_, es⟩
  intro i hiS
  obtain ⟨hle, ht⟩ := hs i hiS
  refine ⟨lt_of_le_of_ne hle ?_, ht⟩
  intro he
  subst i
  rcases ht with hraw | hand
  · exact (Nat.not_lt_of_ge lo) hraw
  · rw [hor] at hand
    cases hand
