import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2549_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f1 f2 : ℕ → Bool)
    (h : ∀ r, f1 r = true → f2 r = true) :
    g.op.eval (g.inputs.map f1) = true → g.op.eval (g.inputs.map f2) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun h1 r hr => h r (h1 r hr)
  · rw [hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨r, hr, h1⟩
    exact ⟨r, hr, h r h1⟩

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (l1 l2 : List Bool), l1.length = l2.length →
    (∀ i, l1.getD i false = true → l2.getD i false = true) →
    ∀ i, (drun gs l1).getD i false = true → (drun gs l2).getD i false = true := by
  induction gs with
  | nil => intro l1 l2 _ h; exact h
  | cons g gs ih =>
    intro l1 l2 hl h
    rw [drun_cons, drun_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    · simp [hl]
    · intro i hi
      rcases lt_trichotomy i l1.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero]
        exact gate_mono g (hgs g (by simp)) _ _ h hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

lemma ofFn9 (y : Fin 9 → Bool) : List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, y 8] := rfl

lemma inp_mono (y1 y2 : Fin 9 → Bool) (h : ∀ i, y1 i = true → y2 i = true) :
    ∀ i, (List.ofFn y1 ++ [y1 0 || y1 4]).getD i false = true →
      (List.ofFn y2 ++ [y2 0 || y2 4]).getD i false = true := by
  intro i hi
  rw [ofFn9] at hi
  rw [ofFn9]
  by_cases hlt : i < 10
  · interval_cases i
    all_goals first
      | exact h _ hi
      | (simp only [List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero,
          Bool.or_eq_true] at hi ⊢
         rcases hi with hi | hi
         · exact Or.inl (h 0 hi)
         · exact Or.inr (h 4 hi))
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact absurd hi (by simp)

def f9 (x : Fin 9 → Bool) : Bool :=
  [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x x6.1 && x x6.2

def T9 : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def F9 : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]

lemma expand (x : Fin 9 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
  funext i
  fin_cases i <;> rfl

lemma up_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    f9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = true →
      ∃ n ∈ T9, ∀ i : Fin 9, n.testBit i = true → ![b0, b1, b2, b3, b4, b5, b6, b7, b8] i = true := by
  decide +kernel

lemma down_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    f9 ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = false →
      ∃ n ∈ F9, ∀ i : Fin 9, ![b0, b1, b2, b3, b4, b5, b6, b7, b8] i = true → n.testBit i = true := by
  decide +kernel

lemma up (x : Fin 9 → Bool) (h : f9 x = true) :
    ∃ n ∈ T9, ∀ i : Fin 9, n.testBit i = true → x i = true := by
  rw [expand x] at h ⊢
  exact up_all _ _ _ _ _ _ _ _ _ h

lemma down (x : Fin 9 → Bool) (h : f9 x = false) :
    ∃ n ∈ F9, ∀ i : Fin 9, x i = true → n.testBit i = true := by
  rw [expand x] at h ⊢
  exact down_all _ _ _ _ _ _ _ _ _ h

lemma memT : ∀ n ∈ T9, n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)] := by
  decide

lemma memF : ∀ n ∈ F9, n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)] := by
  decide

lemma FnT : ∀ n ∈ F9, n ∉ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)] := by
  decide

lemma TT : ∀ n ∈ T9, n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)] := by
  decide

theorem m49 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) x4 := by
  intro C hmono hpts x
  have hao : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hmono g hg).1
    simpa using this
  have gm : ∀ y1 y2 : Fin 9 → Bool, (∀ i, y1 i = true → y2 i = true) →
      C.eval (List.ofFn y1 ++ [y1 0 || y1 4]) = true →
        C.eval (List.ofFn y2 ++ [y2 0 || y2 4]) = true := by
    intro y1 y2 h h1
    exact run_mono C.gates hao _ _ (by simp) (inp_mono y1 y2 h) C.output h1
  change C.eval (List.ofFn x ++ [x 0 || x 4]) = f9 x
  cases hf : f9 x
  · obtain ⟨n, hn, hsub⟩ := down x hf
    have hv := hpts n (memF n hn)
    simp only [FnT n hn, decide_false] at hv
    by_contra hc
    have h1 := gm x (fun i => n.testBit i) hsub (by simpa using hc)
    rw [hv] at h1
    exact Bool.false_ne_true h1
  · obtain ⟨n, hn, hsub⟩ := up x hf
    have hv := hpts n (memT n hn)
    simp only [TT n hn, decide_true] at hv
    exact gm (fun i => n.testBit i) x hsub hv

end PEqualNP.Outside.L_meta_2549_aux

theorem PEqualNP.Outside.L_meta_2549 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) x4 :=
  PEqualNP.Outside.L_meta_2549_aux.m49
