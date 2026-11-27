import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4809 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (42 : ℕ)) (x3 x4 : Fin (43 : ℕ)) (x5 : (Fin (42 : ℕ) → Bool) → Prop),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x7 : Fin (42 : ℕ) → Bool),         ((x5 x7 ∧ ∀ (x8 : Fin (42 : ℕ) → Bool), (∀ (x9 : Fin (42 : ℕ)), x8 x9 = Bool.true → x7 x9 = Bool.true) → x5 x8 → x8 = x7) ∨ ¬x5 x7 ∧ ∀ (x8 : Fin (42 : ℕ) → Bool), (∀ (x9 : Fin (42 : ℕ)), x7 x9 = Bool.true → x8 x9 = Bool.true) → ¬x5 x8 → x8 = x7) →           have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin (43 : ℕ)) => Fin.lastCases (x7 (0 : Fin (42 : ℕ)) || x7 x2) x7 x9;           x1.eval (List.ofFn fun (x10 : Fin (44 : ℕ)) => Fin.lastCases (x9 x3 || x9 x4) x9 x10) = Bool.true ↔ x5 x7) →       ∀ (x8 : Fin (42 : ℕ) → Bool),         have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin (43 : ℕ)) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x2) x8 x9;         x1.eval (List.ofFn fun (x10 : Fin (44 : ℕ)) => Fin.lastCases (x9 x3 || x9 x4) x9 x10) = Bool.true ↔ x5 x8 := by
  intro x1 x2 x3 x4 x5 hmono hyp x8
  have getD_mono : ∀ (a b : List Bool), List.Forall₂ (fun p q : Bool => p = true → q = true) a b →
      ∀ i : ℕ, a.getD i false = true → b.getD i false = true := by
    intro a b hab
    induction hab with
    | nil => intro i h; simp at h
    | cons hpq _ ih =>
      intro i h
      cases i with
      | zero => simpa using hpq (by simpa using h)
      | succ k => simpa using ih k (by simpa using h)
  have step_mono : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool), (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      List.Forall₂ (fun p q : Bool => p = true → q = true) w w' →
      g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
    intro g w w' hop hw h
    rcases hop with hop | hop
    · rw [hop] at h ⊢
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map] at h ⊢
      rintro _ ⟨a, ha, rfl⟩
      exact getD_mono w w' hw a (h _ ⟨a, ha, rfl⟩)
    · rw [hop] at h ⊢
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map] at h ⊢
      obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := h
      exact ⟨_, ⟨a, ha, rfl⟩, getD_mono w w' hw a hv⟩
  have wires_mono : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool),
      (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      List.Forall₂ (fun p q : Bool => p = true → q = true) w w' →
      List.Forall₂ (fun p q : Bool => p = true → q = true)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
    intro gs
    induction gs with
    | nil => intro w w' _ h; exact h
    | cons g gs ih =>
      intro w w' hg h
      simp only [List.foldl_cons]
      apply ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      exact List.rel_append h (List.Forall₂.cons (step_mono g w w' (hg g (by simp)) h) List.Forall₂.nil)
  have hops : ∀ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    simpa using (hmono g hg).1
  have eval_mono : ∀ (a b : List Bool), List.Forall₂ (fun p q : Bool => p = true → q = true) a b → x1.eval a = true → x1.eval b = true := by
    intro a b hab h
    exact getD_mono _ _ (wires_mono x1.gates a b hops hab) _ h
  have Fmono : ∀ x y : Fin 42 → Bool, (∀ i, x i = true → y i = true) →
      x1.eval (List.ofFn fun k : Fin 44 => (Fin.lastCases (motive := fun _ => Bool) ((Fin.lastCases (motive := fun _ => Bool) (x 0 || x x2) x x3) || (Fin.lastCases (motive := fun _ => Bool) (x 0 || x x2) x x4)) (Fin.lastCases (motive := fun _ => Bool) (x 0 || x x2) x) k)) = true → x1.eval (List.ofFn fun k : Fin 44 => (Fin.lastCases (motive := fun _ => Bool) ((Fin.lastCases (motive := fun _ => Bool) (y 0 || y x2) y x3) || (Fin.lastCases (motive := fun _ => Bool) (y 0 || y x2) y x4)) (Fin.lastCases (motive := fun _ => Bool) (y 0 || y x2) y) k)) = true := by
    intro x y hxy
    have e1 : ∀ k : Fin 43, Fin.lastCases (motive := fun _ => Bool) (x 0 || x x2) x k = true →
        Fin.lastCases (motive := fun _ => Bool) (y 0 || y x2) y k = true := by
      intro k
      induction k using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Bool.or_eq_true]
        exact fun h => h.imp (hxy _) (hxy _)
      | cast j =>
        simp only [Fin.lastCases_castSucc]
        exact hxy j
    apply eval_mono
    rw [List.forall₂_iff_get]
    refine ⟨by simp, ?_⟩
    intro i h1 h2
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    generalize (⟨i, _⟩ : Fin 44) = k
    induction k using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last, Bool.or_eq_true]
      exact fun h => h.imp (e1 _) (e1 _)
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact e1 j
  by_cases h5 : x5 x8
  · obtain ⟨m, hm_le, hm_min⟩ := exists_minimal_le_of_wellFoundedLT x5 x8 h5
    have hFm : x1.eval (List.ofFn fun k : Fin 44 => (Fin.lastCases (motive := fun _ => Bool) ((Fin.lastCases (motive := fun _ => Bool) (m 0 || m x2) m x3) || (Fin.lastCases (motive := fun _ => Bool) (m 0 || m x2) m x4)) (Fin.lastCases (motive := fun _ => Bool) (m 0 || m x2) m) k)) = true :=
      (hyp m (Or.inl ⟨hm_min.1, fun z hz hz5 =>
        le_antisymm (fun i => Bool.le_iff_imp.mpr (hz i)) (hm_min.2 hz5 (fun i => Bool.le_iff_imp.mpr (hz i)))⟩)).mpr hm_min.1
    exact ⟨fun _ => h5, fun _ => Fmono m x8 (fun i => Bool.le_iff_imp.mp (hm_le i)) hFm⟩
  · obtain ⟨M, hM_le, hM_max⟩ := exists_maximal_ge_of_wellFoundedGT (fun z => ¬ x5 z) x8 h5
    have hFM : ¬ x1.eval (List.ofFn fun k : Fin 44 => (Fin.lastCases (motive := fun _ => Bool) ((Fin.lastCases (motive := fun _ => Bool) (M 0 || M x2) M x3) || (Fin.lastCases (motive := fun _ => Bool) (M 0 || M x2) M x4)) (Fin.lastCases (motive := fun _ => Bool) (M 0 || M x2) M) k)) = true := fun hF =>
      hM_max.1 ((hyp M (Or.inr ⟨hM_max.1, fun z hz hz5 =>
        le_antisymm (hM_max.2 hz5 (fun i => Bool.le_iff_imp.mpr (hz i))) (fun i => Bool.le_iff_imp.mpr (hz i))⟩)).mp hF)
    exact ⟨fun hF => absurd (Fmono x8 M (fun i => Bool.le_iff_imp.mp (hM_le i)) hF) hFM, fun h => absurd h h5⟩
