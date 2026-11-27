import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4427

open PEqualNP.CircuitLowerBounds

def Reads (g : Gate) (v : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs

def F (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) : (step w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem eval_indep (g : Gate) (v : ℕ) (hr : ¬ Reads g v) (f f' : ℕ → Bool)
    (h : ∀ i, i ≠ v → f i = f' i) : g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  by_cases hop : g.op = GateOp.not
  · rw [hop]
    have hh : g.inputs.head? ≠ some v := fun e => hr (Or.inl ⟨hop, e⟩)
    cases hi : g.inputs with
    | nil => rfl
    | cons a l =>
      rw [hi] at hh
      have hav : a ≠ v := by
        intro e
        apply hh
        simp [e]
      simp [GateOp.eval, h a hav]
  · have hv : v ∉ g.inputs := fun e => hr (Or.inr ⟨hop, e⟩)
    congr 1
    apply List.map_congr_left
    intro a ha
    exact h a (fun e => hv (e ▸ ha))

theorem indep (v : ℕ) (gs : List Gate) : ∀ (w w' : List Bool), (∀ g ∈ gs, ¬ Reads g v) →
    w.length = w'.length → v < w.length → (∀ i, i ≠ v → w.getD i false = w'.getD i false) →
    ∀ i, i ≠ v → (gs.foldl step w).getD i false = (gs.foldl step w').getD i false := by
  induction gs with
  | nil => intro w w' _ _ _ h i hi; simpa using h i hi
  | cons g gs ih =>
    intro w w' hall hl hv h
    simp only [List.foldl_cons]
    apply ih (step w g) (step w' g) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · simp [step]; omega
    · intro i hi
      rw [step_getD, step_getD, hl]
      split_ifs with h1 h2
      · exact h i hi
      · exact eval_indep g v (hall g List.mem_cons_self) _ _ h
      · rfl

theorem keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih (step w g) i (by simp [step]; omega), step_getD, if_pos hi]

def base (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2]

def nv (L : List (Fin 11)) (x : Fin 9 → Bool) : Bool :=
  GateOp.not.eval (L.map fun k : Fin 11 => (base x).getD k.val false)

def inp (L : List (Fin 11)) (x : Fin 9 → Bool) : List Bool := base x ++ [nv L x]

theorem base_len (x : Fin 9 → Bool) : (base x).length = 10 := by simp [base]

theorem base_lt (x : Fin 9 → Bool) (i : ℕ) (h : i < 9) : (base x).getD i false = x ⟨i, h⟩ := by
  unfold base
  rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
    List.getElem_ofFn]

theorem base_nine (x : Fin 9 → Bool) : (base x).getD 9 false = (x 0 || x 2) := by
  unfold base
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

def tab : List (List ℕ) := [[2, 4], [6], [0, 7], [8], [3], [7], [1], [5], [6]]

def A (v : Fin 9) (i : Fin 9) : Bool := decide (i.val ∈ tab.getD v.val [])

def B (v : Fin 9) (i : Fin 9) : Bool := decide (i = v) || A v i

theorem T1 : ∀ v : Fin 9, F (A v) = false ∧ F (B v) = true ∧
    (A v 0 || A v 2) = (B v 0 || B v 2) ∧ F (fun i => decide (i = v)) = false := by
  decide

theorem main (L : List (Fin 11)) (C : Circuit) (H : ∀ x : Fin 9 → Bool, C.eval (inp L x) = F x)
    (v : Fin 9) (hh : L.head? ≠ some (Fin.castAdd 2 v)) : ∃ g ∈ C.gates, Reads g v.val := by
  by_contra hne
  have hall : ∀ g ∈ C.gates, ¬ Reads g v.val := fun g hg hr => hne ⟨g, hg, hr⟩
  obtain ⟨t1, t2, t3, t4⟩ := T1 v
  have hv9 : v.val < 9 := v.isLt
  have hbase : ∀ i, i ≠ v.val → (base (A v)).getD i false = (base (B v)).getD i false := by
    intro i hi
    rcases Nat.lt_or_ge i 9 with h1 | h1
    · rw [base_lt _ i h1, base_lt _ i h1]
      have : (⟨i, h1⟩ : Fin 9) ≠ v := fun e => hi (by rw [← e])
      simp [B, this]
    · rcases Nat.lt_or_ge i 10 with h2 | h2
      · have e : i = 9 := by omega
        rw [e, base_nine, base_nine]
        exact t3
      · rw [List.getD_eq_default _ _ (by rw [base_len]; exact h2),
          List.getD_eq_default _ _ (by rw [base_len]; exact h2)]
  have hnv : nv L (A v) = nv L (B v) := by
    unfold nv
    cases hL : L with
    | nil => rfl
    | cons a l =>
      rw [hL] at hh
      have hav : a.val ≠ v.val := by
        intro e
        apply hh
        have e2 : a = Fin.castAdd 2 v := Fin.ext (by simpa using e)
        rw [e2]
        rfl
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      rw [hbase a.val hav]
  have hin : ∀ i, i ≠ v.val → (inp L (A v)).getD i false = (inp L (B v)).getD i false := by
    intro i hi
    unfold inp
    rcases Nat.lt_or_ge i 10 with h2 | h2
    · rw [List.getD_append _ _ _ _ (by rw [base_len]; exact h2),
        List.getD_append _ _ _ _ (by rw [base_len]; exact h2)]
      exact hbase i hi
    · rw [List.getD_append_right _ _ _ _ (by rw [base_len]; exact h2),
        List.getD_append_right _ _ _ _ (by rw [base_len]; exact h2), base_len, base_len, hnv]
  have hw := indep v.val C.gates (inp L (A v)) (inp L (B v)) hall
    (by simp [inp, base_len]) (by simp [inp, base_len]; omega) hin
  by_cases ho : C.output = v.val
  · have e := H (fun i => decide (i = v))
    unfold Circuit.eval at e
    rw [wires_eq, ho, keep C.gates _ v.val (by simp [inp, base_len]; omega), t4] at e
    unfold inp at e
    rw [List.getD_append _ _ _ _ (by rw [base_len]; omega), base_lt _ _ hv9] at e
    simp at e
  · have e1 := H (A v)
    have e2 := H (B v)
    unfold Circuit.eval at e1 e2
    rw [wires_eq] at e1 e2
    rw [t1] at e1
    rw [t2] at e2
    have e3 := hw C.output ho
    rw [e1, e2] at e3
    exact absurd e3 (by simp)

end PEqualNP.Outside.L_meta_4427

theorem PEqualNP.Outside.L_meta_4427 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : List (Fin (11 : ℕ))) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x4 : Fin (9 : ℕ) → Bool),       have x5 : List Bool := List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))];       x3.eval (x5 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x6 : Fin (11 : ℕ)) => x5.getD (↑x6) Bool.false) x2)]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) →     ∀ (x5 : Fin (9 : ℕ)), x2.head? ≠ Option.some (Fin.castAdd (2 : ℕ) x5) → ∃ x7 ∈ x3.gates, x1 x7 ↑x5 := by
  intro x1 L C H v hh
  exact L_meta_4427.main L C H v hh
