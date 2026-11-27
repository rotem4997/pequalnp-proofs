import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17110

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem foldl_stable (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [List.length_append]; omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

theorem wire_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := foldl_stable C.gates x i hi

theorem wire_first (C : Circuit) (g : Gate) (rest : List Gate) (h : C.gates = g :: rest)
    (x : List Bool) :
    (C.wires x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  unfold Circuit.wires
  rw [h, List.foldl_cons, foldl_stable _ _ _ (by rw [List.length_append]; simp)]
  simp [List.getD_eq_getElem?_getD]

theorem v_lt_gen (n : ℕ) (y : Fin n → Bool) (a : ℕ) (h : a < n) :
    (List.ofFn y).getD a false = y ⟨a, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem v_lt (y : Fin 9 → Bool) (a : ℕ) (h : a < 9) :
    (List.ofFn y).getD a false = y ⟨a, h⟩ := v_lt_gen 9 y a h

theorem v_ge (y : Fin 9 → Bool) (a : ℕ) (h : 9 ≤ a) :
    (List.ofFn y).getD a false = false := by
  simp [List.getD_eq_getElem?_getD, h]

theorem shape (op : GateOp) (ins : List ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (ha : ∃ x y : Fin 9 → Bool,
      op.eval (ins.map fun i => (List.ofFn x).getD i false)
        ≠ op.eval (ins.map fun i => (List.ofFn y).getD i false))
    (hb : ∀ i : ℕ, i < 9 → ∃ x : Fin 9 → Bool,
      (List.ofFn x).getD i false ≠ op.eval (ins.map fun i => (List.ofFn x).getD i false)) :
    ∃ i : Fin 9,
      (∀ y : Fin 9 → Bool, op.eval (ins.map fun k => (List.ofFn y).getD k false) = !(y i)) ∨
      (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
        op.eval (ins.map fun k => (List.ofFn y).getD k false) = (y i && y j)) ∨
      (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
        op.eval (ins.map fun k => (List.ofFn y).getD k false) = (y i || y j)) := by
  have hconst : ∀ c : Bool, ¬ ∀ y : Fin 9 → Bool,
      op.eval (ins.map fun i => (List.ofFn y).getD i false) = c := by
    intro c hc
    obtain ⟨x, y, hxy⟩ := ha
    exact hxy (by rw [hc x, hc y])
  have hwire : ∀ a : ℕ, ¬ ∀ y : Fin 9 → Bool,
      op.eval (ins.map fun i => (List.ofFn y).getD i false) = (List.ofFn y).getD a false := by
    intro a hw
    by_cases h9 : a < 9
    · obtain ⟨x, hx⟩ := hb a h9
      exact hx (hw x).symm
    · exact hconst false (fun y => by rw [hw y, v_ge y a (by omega)])
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact absurd (fun y => by simp [GateOp.eval]) (hconst true)
    · exact absurd (fun y => by simp [GateOp.eval]) (hwire a)
    · have hW : ∀ y : Fin 9 → Bool,
          GateOp.and.eval ([a, b].map fun i => (List.ofFn y).getD i false)
            = ((List.ofFn y).getD a false && (List.ofFn y).getD b false) :=
        fun y => by simp [GateOp.eval]
      by_cases ha9 : a < 9
      · by_cases hb9 : b < 9
        · rcases Nat.lt_trichotomy a b with hlt | heq | hgt
          · exact ⟨⟨a, ha9⟩, Or.inr (Or.inl ⟨⟨b, hb9⟩, Fin.mk_lt_mk.mpr hlt,
              fun y => by rw [hW y, v_lt y a ha9, v_lt y b hb9]⟩)⟩
          · subst heq
            exact absurd (fun y => by rw [hW y, Bool.and_self]) (hwire a)
          · exact ⟨⟨b, hb9⟩, Or.inr (Or.inl ⟨⟨a, ha9⟩, Fin.mk_lt_mk.mpr hgt,
              fun y => by rw [hW y, v_lt y a ha9, v_lt y b hb9, Bool.and_comm]⟩)⟩
        · exact absurd (fun y => by rw [hW y, v_ge y b (by omega), Bool.and_false])
            (hconst false)
      · exact absurd (fun y => by rw [hW y, v_ge y a (by omega), Bool.false_and])
          (hconst false)
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact absurd (fun y => by simp [GateOp.eval]) (hconst false)
    · exact absurd (fun y => by simp [GateOp.eval]) (hwire a)
    · have hW : ∀ y : Fin 9 → Bool,
          GateOp.or.eval ([a, b].map fun i => (List.ofFn y).getD i false)
            = ((List.ofFn y).getD a false || (List.ofFn y).getD b false) :=
        fun y => by simp [GateOp.eval]
      by_cases ha9 : a < 9
      · by_cases hb9 : b < 9
        · rcases Nat.lt_trichotomy a b with hlt | heq | hgt
          · exact ⟨⟨a, ha9⟩, Or.inr (Or.inr ⟨⟨b, hb9⟩, Fin.mk_lt_mk.mpr hlt,
              fun y => by rw [hW y, v_lt y a ha9, v_lt y b hb9]⟩)⟩
          · subst heq
            exact absurd (fun y => by rw [hW y, Bool.or_self]) (hwire a)
          · exact ⟨⟨b, hb9⟩, Or.inr (Or.inr ⟨⟨a, ha9⟩, Fin.mk_lt_mk.mpr hgt,
              fun y => by rw [hW y, v_lt y a ha9, v_lt y b hb9, Bool.or_comm]⟩)⟩
        · exact absurd (fun y => by rw [hW y, v_ge y b (by omega), Bool.or_false])
            (hwire a)
      · exact absurd (fun y => by rw [hW y, v_ge y a (by omega), Bool.false_or])
          (hwire b)
    · simp at hlen
  · rcases ins with _ | ⟨a, rest⟩
    · exact absurd (fun y => by simp [GateOp.eval]) (hconst true)
    · have hW : ∀ y : Fin 9 → Bool,
          GateOp.not.eval ((a :: rest).map fun i => (List.ofFn y).getD i false)
            = !((List.ofFn y).getD a false) :=
        fun y => by simp [GateOp.eval]
      by_cases ha9 : a < 9
      · exact ⟨⟨a, ha9⟩, Or.inl (fun y => by rw [hW y, v_lt y a ha9])⟩
      · exact absurd (fun y => by rw [hW y, v_ge y a (by omega)]; rfl) (hconst true)

theorem core (f : (Fin 9 → Bool) → Bool) (hF : f (fun _ => false) = false)
    (hT : f (fun _ => true) = true)
    (hS : ∀ k : Fin 9, f (fun i => decide (i = k)) = false)
    (hred : ∀ C : Circuit, IsMinimalCircuit 9 C →
      (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) →
      (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧
      (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (hcase : ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C →
      ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y i)) ∨
        (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y i && y j)) ∨
        (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool,
          (C.wires (List.ofFn y)).getD 9 false = (y i || y j))) →
      circuitFun 9 C = f → 16 ≤ C.size) :
    ∀ t : ℕ, HasCircuitSize 9 f t → 16 ≤ t := by
  intro t ht
  obtain ⟨C, hC, hCt, hCe⟩ := ht
  have hCf : circuitFun 9 C = f := funext hCe
  have hex : ∃ s : ℕ, ∃ E : Circuit, FanInTwo E ∧ circuitFun 9 E = f ∧ E.size = s :=
    ⟨C.size, C, hC, hCf, rfl⟩
  classical
  obtain ⟨D, hD, hDf, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ E : Circuit, FanInTwo E → circuitFun 9 E = f → D.size ≤ E.size := by
    intro E hE hEf
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hE, hEf, rfl⟩
  have hDmin : IsMinimalCircuit 9 D := ⟨hD, fun E hE hEf => hmin E hE (hEf.trans hDf)⟩
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y :=
    ⟨fun _ => false, fun _ => true, by rw [hDf, hF, hT]; decide⟩
  obtain ⟨hA, hB⟩ := hred D hDmin hnc
  have hDC : D.size ≤ C.size := hmin C hC hCf
  cases hg : D.gates with
  | nil =>
    exfalso
    have hval : ∀ y : Fin 9 → Bool, f y = (List.ofFn y).getD D.output false := by
      intro y
      rw [← hDf]
      show (D.wires (List.ofFn y)).getD D.output false = _
      unfold Circuit.wires
      rw [hg]
      rfl
    by_cases ho : D.output < 9
    · have h1 := hval (fun i => decide (i = (⟨D.output, ho⟩ : Fin 9)))
      rw [hS, v_lt _ _ ho] at h1
      simp at h1
    · have h1 := hval (fun _ => true)
      rw [hT, v_ge _ _ (by omega)] at h1
      exact Bool.noConfusion h1
  | cons g rest =>
    have hlen : 0 < D.gates.length := by rw [hg]; simp
    have hW : ∀ y : Fin 9 → Bool, (D.wires (List.ofFn y)).getD 9 false
        = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
      intro y
      have h := wire_first D g rest hg (List.ofFn y)
      rw [List.length_ofFn] at h
      exact h
    have hgm : g ∈ D.gates := by rw [hg]; simp
    obtain ⟨hop, hfan⟩ := hD g hgm
    have hop' : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    have ha' : ∃ x y : Fin 9 → Bool,
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
          ≠ g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
      obtain ⟨x, y, hxy⟩ := hA 0 hlen
      exact ⟨x, y, by rw [← hW x, ← hW y]; exact hxy⟩
    have hb' : ∀ i : ℕ, i < 9 → ∃ x : Fin 9 → Bool,
        (List.ofFn x).getD i false
          ≠ g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
      intro i hi
      obtain ⟨x, hx⟩ := hB i 0 (by omega) hlen
      refine ⟨x, ?_⟩
      rw [← hW x, ← wire_input D (List.ofFn x) i (by rw [List.length_ofFn]; exact hi)]
      exact hx
    obtain ⟨i, hi⟩ := shape g.op g.inputs hop' hfan ha' hb'
    have h16 : 16 ≤ D.size := by
      refine hcase i D hD ?_ hDf
      rcases hi with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
      · exact Or.inl (fun y => by rw [hW y, h y])
      · exact Or.inr (Or.inl ⟨j, hj, fun y => by rw [hW y, h y]⟩)
      · exact Or.inr (Or.inr ⟨j, hj, fun y => by rw [hW y, h y]⟩)
    omega

end PEqualNP.Outside.L_meta_17110

theorem PEqualNP.Outside.L_meta_17110 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) t → 16 ≤ t := by
  intro hred h0 h1 h2 h3 h4 h5 h6 h7 h8
  refine PEqualNP.Outside.L_meta_17110.core _ (by decide) (by decide) (by decide)
    (fun C hm hn => ⟨(hred 9 C hm hn).1, (hred 9 C hm hn).2.1⟩) ?_
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
    revert i
    decide
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
