import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17107

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pf (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma getD_snoc_lt (l : List Bool) (x : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (l : List Bool) (x : Bool) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i false = x := by
  subst hi
  simp [List.getD]

lemma stepW_length (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

lemma fold_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (stepW w g) i (by rw [stepW_length]; omega)]
    exact getD_snoc_lt w _ i hi

lemma ofFn_getD_lt_gen {n : ℕ} (y : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn y).getD i false = y ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]

lemma ofFn_getD_lt (y : Fin 9 → Bool) (i : ℕ) (h : i < 9) :
    (List.ofFn y).getD i false = y ⟨i, h⟩ :=
  ofFn_getD_lt_gen y i h

lemma ofFn_getD_ge (y : Fin 9 → Bool) (i : ℕ) (h : 9 ≤ i) :
    (List.ofFn y).getD i false = false :=
  List.getD_eq_default _ _ (by rw [List.length_ofFn]; exact h)

def valIn (y : Fin 9 → Bool) (i : ℕ) : Bool := (List.ofFn y).getD i false

lemma valIn_lt (y : Fin 9 → Bool) (i : ℕ) (h : i < 9) : valIn y i = y ⟨i, h⟩ :=
  ofFn_getD_lt y i h

lemma valIn_ge (y : Fin 9 → Bool) (i : ℕ) (h : 9 ≤ i) : valIn y i = false :=
  ofFn_getD_ge y i h

def w9 (C : Circuit) (y : Fin 9 → Bool) : Bool := (C.wires (List.ofFn y)).getD 9 false

lemma w9_first (C : Circuit) (g0 : Gate) (rest : List Gate) (hg : C.gates = g0 :: rest)
    (y : Fin 9 → Bool) : w9 C y = g0.op.eval (g0.inputs.map (valIn y)) := by
  have h1 : (rest.foldl stepW (stepW (List.ofFn y) g0)).getD 9 false
      = (stepW (List.ofFn y) g0).getD 9 false :=
    fold_getD_lt rest (stepW (List.ofFn y) g0) 9 (by rw [stepW_length, List.length_ofFn]; omega)
  have h2 : (stepW (List.ofFn y) g0).getD 9 false = g0.op.eval (g0.inputs.map (valIn y)) :=
    getD_snoc_eq (List.ofFn y) (g0.op.eval (g0.inputs.map (valIn y))) 9
      (by rw [List.length_ofFn])
  have h3 : w9 C y = (rest.foldl stepW (stepW (List.ofFn y) g0)).getD 9 false := by
    show (C.wires (List.ofFn y)).getD 9 false = _
    rw [wires_eq, hg, List.foldl_cons]
  exact h3.trans (h1.trans h2)

lemma wires_input (C : Circuit) (y : Fin 9 → Bool) (i : ℕ) (h : i < 9) :
    (C.wires (List.ofFn y)).getD i false = y ⟨i, h⟩ := by
  rw [wires_eq, fold_getD_lt C.gates (List.ofFn y) i (by rw [List.length_ofFn]; exact h)]
  exact ofFn_getD_lt y i h

lemma gateShape (op : GateOp) (ins : List ℕ) (w : (Fin 9 → Bool) → Bool)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : ins.length ≤ 2)
    (hw : ∀ y, w y = op.eval (ins.map (valIn y)))
    (hnc : ∃ x y : Fin 9 → Bool, w x ≠ w y)
    (hne : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ w x) :
    (∃ a : Fin 9, ∀ y, w y = !(y a)) ∨
    (∃ a b : Fin 9, a ≠ b ∧ ∀ y, w y = (y a && y b)) ∨
    (∃ a b : Fin 9, a ≠ b ∧ ∀ y, w y = (y a || y b)) := by
  have hconst : ∀ c : Bool, (∀ y, w y = c) → False := by
    intro c h
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((h x).trans (h y).symm)
  have hproj : ∀ (i : ℕ), i < 9 → (∀ y, w y = valIn y i) → False := by
    intro i hi h
    obtain ⟨x, hx⟩ := hne ⟨i, hi⟩
    exact hx ((valIn_lt x i hi).symm.trans (h x).symm)
  have hone : ∀ (i : ℕ), (∀ y, w y = valIn y i) → False := by
    intro i h
    by_cases hi : i < 9
    · exact hproj i hi h
    · exact hconst false (fun y => (h y).trans (valIn_ge y i (by omega)))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact (hconst true (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · exact (hone a (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · have h : ∀ y, w y = (valIn y a && valIn y b) :=
        fun y => (hw y).trans (by simp [GateOp.eval])
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · by_cases hab : a = b
          · exact (hproj a ha (fun y => by rw [h y, ← hab, Bool.and_self])).elim
          · right; left
            refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
            · intro hh
              exact hab (congrArg Fin.val hh)
            · intro y
              rw [h y, valIn_lt y a ha, valIn_lt y b hb]
        · exact (hconst false (fun y => by
            rw [h y, valIn_ge y b (by omega), Bool.and_false])).elim
      · exact (hconst false (fun y => by
          rw [h y, valIn_ge y a (by omega), Bool.false_and])).elim
    · exact absurd hlen (by simp only [List.length_cons]; omega)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact (hconst false (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · exact (hone a (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · have h : ∀ y, w y = (valIn y a || valIn y b) :=
        fun y => (hw y).trans (by simp [GateOp.eval])
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · by_cases hab : a = b
          · exact (hproj a ha (fun y => by rw [h y, ← hab, Bool.or_self])).elim
          · right; right
            refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_⟩
            · intro hh
              exact hab (congrArg Fin.val hh)
            · intro y
              rw [h y, valIn_lt y a ha, valIn_lt y b hb]
        · exact (hproj a ha (fun y => by
            rw [h y, valIn_ge y b (by omega), Bool.or_false])).elim
      · exact (hone b (fun y => by
          rw [h y, valIn_ge y a (by omega), Bool.false_or])).elim
    · exact absurd hlen (by simp only [List.length_cons]; omega)
  · rcases ins with _ | ⟨a, rest⟩
    · exact (hconst true (fun y => (hw y).trans (by simp [GateOp.eval]))).elim
    · have h : ∀ y, w y = !(valIn y a) :=
        fun y => (hw y).trans (by simp [GateOp.eval])
      by_cases ha : a < 9
      · left
        exact ⟨⟨a, ha⟩, fun y => by rw [h y, valIn_lt y a ha]⟩
      · exact (hconst true (fun y => by simp [h y, valIn_ge y a (by omega)])).elim

lemma pf_single : ∀ k : Fin 9, pf (fun i => decide (i = k)) = false := by
  decide +kernel

lemma no_empty (C : Circuit) (hg : C.gates = []) (hf : circuitFun 9 C = pf) : False := by
  have hev : ∀ y : Fin 9 → Bool, (List.ofFn y).getD C.output false = pf y := by
    intro y
    have h := congrFun hf y
    have h2 : circuitFun 9 C y = (List.ofFn y).getD C.output false := by
      show (C.wires (List.ofFn y)).getD C.output false = _
      rw [wires_eq, hg, List.foldl_nil]
    exact h2.symm.trans h
  by_cases ho : C.output < 9
  · have h := hev (fun i : Fin 9 => decide (i = (⟨C.output, ho⟩ : Fin 9)))
    have h1 := ofFn_getD_lt (fun i : Fin 9 => decide (i = (⟨C.output, ho⟩ : Fin 9))) C.output ho
    have h2 := pf_single ⟨C.output, ho⟩
    have h3 : decide ((⟨C.output, ho⟩ : Fin 9) = ⟨C.output, ho⟩) = false :=
      h1.symm.trans (h.trans h2)
    simp at h3
  · have h := hev (fun _ => true)
    rw [ofFn_getD_ge _ _ (by omega)] at h
    exact absurd h (by decide)

lemma minimal_ge
    (H : ∀ C : Circuit, IsMinimalCircuit 9 C → (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧ (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (HC : ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C → ((∀ y : Fin 9 → Bool, w9 C y = !(y i)) ∨ (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, w9 C y = (y i && y j)) ∨ (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, w9 C y = (y i || y j))) → circuitFun 9 C = pf → 16 ≤ C.size)
    (C : Circuit) (hmin : IsMinimalCircuit 9 C) (hf : circuitFun 9 C = pf) : 16 ≤ C.size := by
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y :=
    ⟨fun _ => false, fun _ => true, by rw [hf]; decide⟩
  obtain ⟨ha, hb⟩ := H C hmin hnc
  have hcases : (∃ g0 rest, C.gates = g0 :: rest) ∨ C.gates = [] := by
    cases hc : C.gates with
    | nil => exact Or.inr rfl
    | cons g r => exact Or.inl ⟨g, r, rfl⟩
  rcases hcases with ⟨g0, rest, hg⟩ | hg
  · have hlen : 0 < C.gates.length := by
      rw [hg]
      simp
    have hfan := hmin.1 g0 (by rw [hg]; simp)
    have hnc9 : ∃ x y : Fin 9 → Bool, w9 C x ≠ w9 C y := ha 0 hlen
    have hne9 : ∀ i : Fin 9, ∃ x : Fin 9 → Bool, x i ≠ w9 C x := by
      intro i
      obtain ⟨x, hx⟩ := hb i.val 0 (by have := i.isLt; omega) hlen
      refine ⟨x, ?_⟩
      rw [wires_input C x i.val i.isLt] at hx
      exact hx
    rcases gateShape g0.op g0.inputs (w9 C) hfan.1 hfan.2 (w9_first C g0 rest hg) hnc9 hne9
      with ⟨a, hA⟩ | ⟨a, b, hab, hA⟩ | ⟨a, b, hab, hA⟩
    · exact HC a C hmin.1 (Or.inl hA) hf
    · rcases lt_or_gt_of_ne hab with hlt | hlt
      · exact HC a C hmin.1 (Or.inr (Or.inl ⟨b, hlt, hA⟩)) hf
      · exact HC b C hmin.1 (Or.inr (Or.inl ⟨a, hlt,
          fun y => (hA y).trans (Bool.and_comm _ _)⟩)) hf
    · rcases lt_or_gt_of_ne hab with hlt | hlt
      · exact HC a C hmin.1 (Or.inr (Or.inr ⟨b, hlt, hA⟩)) hf
      · exact HC b C hmin.1 (Or.inr (Or.inr ⟨a, hlt,
          fun y => (hA y).trans (Bool.or_comm _ _)⟩)) hf
  · exact (no_empty C hg hf).elim

lemma all_ge
    (H : ∀ C : Circuit, IsMinimalCircuit 9 C → (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool, (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧ (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (HC : ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C → ((∀ y : Fin 9 → Bool, w9 C y = !(y i)) ∨ (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, w9 C y = (y i && y j)) ∨ (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, w9 C y = (y i || y j))) → circuitFun 9 C = pf → 16 ≤ C.size) :
    ∀ s : ℕ, ∀ C : Circuit, FanInTwo C → C.size = s → circuitFun 9 C = pf → 16 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro C hfan hs hf
    by_cases hmin : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = circuitFun 9 C →
        C.size ≤ D.size
    · have hm : IsMinimalCircuit 9 C := And.intro hfan hmin
      have h := minimal_ge H HC C hm hf
      omega
    · push_neg at hmin
      obtain ⟨D, hD, hDf, hlt⟩ := hmin
      have h := ih D.size (by omega) D hD rfl (hDf.trans hf)
      omega

theorem main_aux : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 16 ≤ t := by
  intro H h0 h1 h2 h3 h4 h5 h6 h7 h8 t ht
  obtain ⟨C, hfan, hsz, hev⟩ := ht
  have HC : ∀ i : Fin 9, ∀ C : Circuit, FanInTwo C → ((∀ y : Fin 9 → Bool, w9 C y = !(y i)) ∨ (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, w9 C y = (y i && y j)) ∨ (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, w9 C y = (y i || y j))) → circuitFun 9 C = pf → 16 ≤ C.size := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  have h := all_ge (fun C hC hnc => ⟨(H 9 C hC hnc).1, (H 9 C hC hnc).2.1⟩) HC C.size C hfan rfl
    (by funext x; exact hev x)
  omega

end PEqualNP.Outside.L_meta_17107

theorem PEqualNP.Outside.L_meta_17107 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 16 ≤ t :=
  PEqualNP.Outside.L_meta_17107.main_aux

