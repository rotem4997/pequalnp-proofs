import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-2748. When neither the NOT gate (gate 1) nor the AND gate (gate 2) reads a
-- wire numbered 10 or more, the two gates are swapped and wires 10 and 11 are renamed in
-- every later gate and in the output; the new circuit has the same size and function and an
-- AND as its second gate, the case of the first hypothesis (the statement of L-meta-2149).
-- The second hypothesis is the remaining case.
theorem PEqualNP.Outside.R_meta_2748_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (16 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x1.gates[(2 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x7 ∧ ∃ x8 ∈ x7.inputs, (10 : ℕ) ≤ x8) ∨ (∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(2 : ℕ)]? = Option.some x7 ∧ ∃ x8 ∈ x7.inputs, (10 : ℕ) ≤ x8) → (16 : ℕ) ≤ x1.size) →
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x1.gates[(2 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (16 : ℕ) ≤ x1.size := by
  intro h1 h2 C hfan h9 hfun hop1 hop2
  have hW : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (y : List Bool), D.wires y
      = D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y :=
    fun _ _ => rfl
  have hEv : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (y : List Bool),
      D.eval y = (D.wires y).getD D.output false := fun _ _ => rfl
  have hCF : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (y : Fin 9 → Bool),
      PEqualNP.MetaComplexity.circuitFun 9 D y = D.eval (List.ofFn y) := fun _ _ => rfl
  have hSz : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit), D.size = D.gates.length := fun _ => rfl
  by_cases hbad : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[(1 : ℕ)]? = Option.some g ∧ ∃ i ∈ g.inputs, (10 : ℕ) ≤ i) ∨ (∃ (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[(2 : ℕ)]? = Option.some g ∧ ∃ i ∈ g.inputs, (10 : ℕ) ≤ i)
  · exact h2 C hfan h9 hfun hop1 hop2 hbad
  obtain ⟨gates, out⟩ := C
  rcases gates with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, rest⟩⟩⟩
  · simp at hop1
  · simp at hop1
  · simp at hop2
  have hi1 : ∀ i ∈ g1.inputs, i < 10 := fun i hi => by
    by_contra hc
    exact hbad (Or.inl ⟨g1, rfl, i, hi, by omega⟩)
  have hi2 : ∀ i ∈ g2.inputs, i < 10 := fun i hi => by
    by_contra hc
    exact hbad (Or.inr ⟨g2, rfl, i, hi, by omega⟩)
  obtain ⟨σ, hσ10, hσ11, hσo⟩ : ∃ σ : ℕ → ℕ, σ 10 = 11 ∧ σ 11 = 10 ∧ ∀ i, i ≠ 10 → i ≠ 11 → σ i = i :=
    ⟨fun i => if i = 10 then 11 else if i = 11 then 10 else i, by simp, by simp,
      fun i h10 h11 => by simp [h10, h11]⟩
  have hσlt : ∀ i m, 12 ≤ m → i < m → σ i < m := by
    intro i m hm hi
    by_cases a : i = 10
    · subst a; rw [hσ10]; omega
    by_cases b : i = 11
    · subst b; rw [hσ11]; omega
    rw [hσo i a b]; exact hi
  -- the wire lists after each gate, as Circuit.wires builds them
  have key : ∀ (rs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
      w.length = w'.length → 12 ≤ w.length → (∀ i, w'.getD (σ i) false = w.getD i false) →
      ∀ i, ((rs.map fun g => (⟨g.op, g.inputs.map σ⟩ : PEqualNP.CircuitLowerBounds.Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (σ i) false
        = (rs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false := by
    intro rs
    induction rs with
    | nil => intro w w' _ _ h i; exact h i
    | cons g rs ih =>
      intro w w' hl hm h
      simp only [List.map_cons, List.foldl_cons]
      have hv : g.op.eval ((g.inputs.map σ).map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      apply ih
      · simp [hl]
      · simp; omega
      · intro i
        rw [hv]
        rcases Nat.lt_trichotomy i w.length with hi | hi | hi
        · rw [List.getD_append _ _ _ _ (by rw [← hl]; exact hσlt i _ hm hi),
            List.getD_append _ _ _ _ hi]
          exact h i
        · have hs : σ i = i := hσo i (by omega) (by omega)
          rw [hs, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          simp [hi, hl]
        · have hs : σ i = i := hσo i (by omega) (by omega)
          rw [hs, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have init : ∀ (w0 : List Bool) (p q : Bool), w0.length = 10 → ∀ i,
      (w0 ++ [q] ++ [p]).getD (σ i) false = (w0 ++ [p] ++ [q]).getD i false := by
    intro w0 p q hl i
    rcases Nat.lt_or_ge i 10 with hi | hi
    · rw [hσo i (by omega) (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hl, hi]
    by_cases a : i = 10
    · subst a; rw [hσ10]; simp [List.getD_eq_getElem?_getD, hl]
    by_cases b : i = 11
    · subst b; rw [hσ11]; simp [List.getD_eq_getElem?_getD, hl]
    rw [hσo i a b, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hw : ∀ (x : Fin 9 → Bool) (i : ℕ),
      (PEqualNP.CircuitLowerBounds.Circuit.wires
        ⟨g0 :: g2 :: g1 :: rest.map (fun g => (⟨g.op, g.inputs.map σ⟩ : PEqualNP.CircuitLowerBounds.Gate)), σ out⟩
        (List.ofFn x)).getD (σ i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g0 :: g1 :: g2 :: rest, out⟩ (List.ofFn x)).getD i false := by
    intro x
    rw [hW, hW]
    simp only [List.foldl_cons]
    set w0 := List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)] with hw0
    have hl0 : w0.length = 10 := by simp [hw0]
    have e1 : ∀ a : Bool, (g1.inputs.map fun i => (w0 ++ [a]).getD i false)
        = g1.inputs.map fun i => w0.getD i false := fun a => by
      apply List.map_congr_left
      intro j hj
      exact List.getD_append _ _ _ _ (by rw [hl0]; exact hi1 j hj)
    have e2 : ∀ a : Bool, (g2.inputs.map fun i => (w0 ++ [a]).getD i false)
        = g2.inputs.map fun i => w0.getD i false := fun a => by
      apply List.map_congr_left
      intro j hj
      exact List.getD_append _ _ _ _ (by rw [hl0]; exact hi2 j hj)
    rw [e1, e2]
    exact key _ _ _ (by simp) (by simp [hl0]) (init w0 _ _ hl0)
  have hsize := h1
    ⟨g0 :: g2 :: g1 :: rest.map (fun g => (⟨g.op, g.inputs.map σ⟩ : PEqualNP.CircuitLowerBounds.Gate)), σ out⟩
    (by
      intro g hg
      simp only [List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | rfl | rfl | ⟨a, ha, rfl⟩
      · exact hfan _ (by simp)
      · exact hfan _ (by simp)
      · exact hfan _ (by simp)
      · have := hfan a (by simp [ha])
        exact ⟨this.1, by simpa using this.2⟩)
    (by
      intro x
      have e := hw x 9
      rw [hσo 9 (by omega) (by omega)] at e
      rw [e]
      exact h9 x)
    (by
      funext x
      have := congrFun hfun x
      rw [hCF, hEv] at this ⊢
      rw [hw x out]
      exact this)
    (by simpa using hop2)
  rw [hSz] at hsize ⊢
  simpa using hsize
