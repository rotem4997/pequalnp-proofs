import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8468_1
    (h_formula : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (42 : ℕ) ≤ x1.output → x1.output < (42 : ℕ) + x1.gates.length → (∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (List.filter (fun (x2 : ℕ) => Decidable.decide ((42 : ℕ) ≤ x2)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ∃ (x4 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x5 ∈ x4, x5.1.Nonempty ∧ x5.2.Nonempty ∧ ∀ x7 ∈ x5.1, ∀ x9 ∈ x5.2, (↑x9 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ (∀ (x5 x6 : Fin (21 : ℕ)), (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x8 ∈ x4, x5 ∈ x8.1 ∧ x6 ∈ x8.2) ∧ ∑ x5 ∈ x4, (x5.1.card + x5.2.card - (1 : ℕ)) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x5.op Bool.false Bool.true Bool.false (fun (x6 : ℕ) => Bool.false) Bool.false) x1.gates + (1 : ℕ))
    (h_shared : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (42 : ℕ) ≤ x1.output → x1.output < (42 : ℕ) + x1.gates.length → (∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ¬ (List.filter (fun (x2 : ℕ) => Decidable.decide ((42 : ℕ) ≤ x2)) (x1.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates)).Nodup → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ∃ (x4 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x5 ∈ x4, x5.1.Nonempty ∧ x5.2.Nonempty ∧ ∀ x7 ∈ x5.1, ∀ x9 ∈ x5.2, (↑x9 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ (∀ (x5 x6 : Fin (21 : ℕ)), (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x8 ∈ x4, x5 ∈ x8.1 ∧ x6 ∈ x8.2) ∧ ∑ x5 ∈ x4, (x5.1.card + x5.2.card - (1 : ℕ)) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x5.op Bool.false Bool.true Bool.false (fun (x6 : ℕ) => Bool.false) Bool.false) x1.gates + (1 : ℕ)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → ∃ (x4 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x5 ∈ x4, x5.1.Nonempty ∧ x5.2.Nonempty ∧ ∀ x7 ∈ x5.1, ∀ x9 ∈ x5.2, (↑x9 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ (∀ (x5 x6 : Fin (21 : ℕ)), (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x8 ∈ x4, x5 ∈ x8.1 ∧ x6 ∈ x8.2) ∧ ∑ x5 ∈ x4, (x5.1.card + x5.2.card - (1 : ℕ)) ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x5.op Bool.false Bool.true Bool.false (fun (x6 : ℕ) => Bool.false) Bool.false) x1.gates + (1 : ℕ) := by
  intro C hm hc
  have hlen_fold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  have hprefix_fold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
        w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) i (by simp; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hs : ∀ u : Fin 42, C.eval (List.ofFn fun i : Fin 42 => decide (i = u)) = false := by
    intro u
    by_contra h
    simp only [Bool.not_eq_false] at h
    obtain ⟨a, b, ⟨h1, h2, _⟩, h3, h4⟩ := (hc _).mp h
    simp at h3 h4
    subst h3
    subst h4
    omega
  have hout_ge : 42 ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < 42 := by omega
    let u : Fin 42 := ⟨C.output, hlt'⟩
    have h1 := hs u
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at h1
    rw [hprefix_fold C.gates (List.ofFn fun i : Fin 42 => decide (i = u)) C.output (by simp [hlt'])] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at h1
    simp only [hlt', dite_true, Option.getD_some, u, decide_true] at h1
    exact Bool.noConfusion h1
  have hout_lt : C.output < 42 + C.gates.length := by
    by_contra hge
    have hge' : 42 + C.gates.length ≤ C.output := by omega
    have ht : C.eval (List.ofFn fun i : Fin 42 => decide (i = 0) || decide (i = 21)) = true := by
      rw [hc]
      exact ⟨0, 21, ⟨by decide, by decide, by decide⟩, by decide, by decide⟩
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at ht
    have hlen : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun i : Fin 42 => decide (i = 0) || decide (i = 21))).length ≤ C.output := by
      rw [hlen_fold]
      simp [hge']
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at ht
    simp at ht
  have hand : ∃ (x2 : Fin C.gates.length), (C.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    by_contra hna
    have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hgm
      have h1 := (hm g hgm).1
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hgm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      rcases h1 with h1 | h1
      · exact absurd ⟨i, h1⟩ hna
      · exact h1
    have hgetD_zip : ∀ (w1 w2 : List Bool), w1.length = w2.length → ∀ i : ℕ,
        (List.zipWith (fun a b => a || b) w1 w2).getD i false = (w1.getD i false || w2.getD i false) := by
      intro w1
      induction w1 with
      | nil => intro w2 h i; cases w2 <;> simp_all
      | cons a t ih =>
        intro w2 h i
        cases w2 with
        | nil => simp at h
        | cons b s =>
          cases i with
          | zero => simp
          | succ i =>
            simp only [List.zipWith_cons_cons, List.getD_cons_succ]
            exact ih s (by simpa using h) i
    have hany_or : ∀ (l : List ℕ) (f g : ℕ → Bool),
        (l.map fun i => f i || g i).any id = ((l.map f).any id || (l.map g).any id) := by
      intro l f g
      induction l with
      | nil => simp
      | cons a t ih =>
        simp only [List.map_cons, List.any_cons, ih, id]
        cases f a <;> cases g a <;> simp
    have hfold_hom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        ∀ (w1 w2 : List Bool), w1.length = w2.length →
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.zipWith (fun a b => a || b) w1 w2) =
        List.zipWith (fun a b => a || b)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
      intro gs
      induction gs with
      | nil => intro _ w1 w2 _; simp
      | cons g gs ih =>
        intro hgs w1 w2 h
        simp only [List.foldl_cons]
        have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.or := hgs g (by simp)
        have hev : ∀ (l : List Bool),
            PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or l = l.any id :=
          fun _ => rfl
        have e : (List.zipWith (fun a b => a || b) w1 w2 ++
            [g.op.eval (g.inputs.map fun i => (List.zipWith (fun a b => a || b) w1 w2).getD i false)]) =
            List.zipWith (fun a b => a || b)
              (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
              (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := by
          rw [List.zipWith_append h, hop, hev, hev, hev]
          simp only [hgetD_zip w1 w2 h, hany_or, List.zipWith_cons_cons, List.zipWith_nil_left]
        rw [e]
        exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (by simp [h])
    have heval_hom : C.eval (List.ofFn fun i : Fin 42 => decide (i = 0) || decide (i = 21)) =
        (C.eval (List.ofFn fun i : Fin 42 => decide (i = 0)) ||
         C.eval (List.ofFn fun i : Fin 42 => decide (i = 21))) := by
      have hz : (List.ofFn fun i : Fin 42 => decide (i = 0) || decide (i = 21)) =
          List.zipWith (fun a b => a || b)
            (List.ofFn fun i : Fin 42 => decide (i = 0))
            (List.ofFn fun i : Fin 42 => decide (i = 21)) := by
        apply List.ext_getElem <;> simp
      unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
      rw [hz, hfold_hom C.gates hg _ _ (by simp), hgetD_zip]
      rw [hlen_fold, hlen_fold]
      simp
    rw [hs 0, hs 21] at heval_hom
    have ht : C.eval (List.ofFn fun i : Fin 42 => decide (i = 0) || decide (i = 21)) = true := by
      rw [hc]
      exact ⟨0, 21, ⟨by decide, by decide, by decide⟩, by decide, by decide⟩
    rw [heval_hom] at ht
    exact absurd ht (by decide)
  by_cases hnd : (List.filter (fun (x2 : ℕ) => Decidable.decide ((42 : ℕ) ≤ x2)) (C.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates)).Nodup
  · exact h_formula C hm hout_ge hout_lt hand hnd hc
  · exact h_shared C hm hout_ge hout_lt hand hnd hc
