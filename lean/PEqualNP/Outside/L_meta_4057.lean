import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4057

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def rg (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rc (ρ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (rg ρ), ρ C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = step (run gs w) g := by
  simp [run, List.foldl_append]

theorem run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih =>
    intro w
    have h := ih (step w g)
    simp only [run, List.foldl_cons] at h ⊢
    rw [h]
    simp [step]
    omega

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) : (step w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem ren (ρ : ℕ → ℕ) (gs : List Gate) : ∀ (w w' : List Bool) (m : ℕ), w.length = m →
    w'.length = m → (∀ i, i < m → ρ i < m) → (∀ i, m ≤ i → ρ i = i) →
    (∀ i, w'.getD (ρ i) false = w.getD i false) →
    ∀ i, ((gs.map (rg ρ)).foldl step w').getD (ρ i) false = (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' m _ _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' m hw hw' hlt hfix hrel
    simp only [List.map_cons, List.foldl_cons]
    apply ih (step w g) (step w' (rg ρ g)) (m + 1)
    · simp [step, hw]
    · simp [step, hw']
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact Nat.lt_succ_of_lt (hlt i h)
      · rw [h, hfix m le_rfl]; exact Nat.lt_succ_self m
    · intro i hi; exact hfix i (Nat.le_of_succ_le hi)
    · intro i
      have hv : (rg ρ g).op.eval ((rg ρ g).inputs.map fun i => w'.getD i false)
          = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [rg, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact hrel a
      simp only [step, hv]
      rcases Nat.lt_or_ge i m with h | h
      · have h2 := hlt i h
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hrel i
      · rw [hfix i h]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hw, hw']

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) (hv : g.op.eval (g.inputs.map f) = true) :
    g.op.eval (g.inputs.map f') = true := by
  rcases hop with h1 | h1
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro b ⟨a, ha, rfl⟩
    exact h a (hv (f a) ⟨a, ha, rfl⟩)
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hv
    exact ⟨f' a, ⟨a, ha, rfl⟩, h a hb⟩

theorem mono_run (gs : List Gate) : ∀ (w w' : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (run gs w).getD i false = true → (run gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ _ h i; simpa [run] using h i
  | cons g gs ih =>
    intro w w' hall hl h
    have h3 := ih (step w g) (step w' g) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      (by simp [step, hl])
      (by
        intro i
        rw [step_getD, step_getD, hl]
        split_ifs with h1 h2
        · exact h i
        · exact eval_mono g (hall g List.mem_cons_self) _ _ h
        · exact id)
    simpa [run] using h3

def V {n : ℕ} (gs : List Gate) (y : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn y)).getD w false

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

theorem V_snoc {n : ℕ} (gs : List Gate) (g : Gate) (y : Fin n → Bool) (w : ℕ) :
    V (gs ++ [g]) y w = if w < n + gs.length then V gs y w
      else if w = n + gs.length then g.op.eval (g.inputs.map fun i => V gs y i) else false := by
  unfold V
  rw [run_snoc, step_getD, run_len, List.length_ofFn]

theorem V_mono {n : ℕ} (gs : List Gate) (hall : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (y y' : Fin n → Bool) (h : ∀ i, y i = true → y' i = true) (w : ℕ) (hw : V gs y w = true) :
    V gs y' w = true := by
  unfold V at hw ⊢
  refine mono_run gs _ _ hall (by simp) ?_ w hw
  intro i hi
  rcases Nat.lt_or_ge i n with h1 | h1
  · rw [getD_ofFn _ i h1] at hi ⊢
    exact h _ hi
  · rw [List.getD_eq_default _ _ (by simpa using h1)] at hi
    exact absurd hi (by simp)

theorem K {n : ℕ} (x : Fin n → Bool) (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    ∀ w, V gs x w = true →
      (∃ u, x u = true ∧ V gs (pairInput u u) w = true) ∨
      (∃ j, j < gs.length ∧ (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
        ∃ u v, x u = true ∧ x v = true ∧ V gs (pairInput u v) (n + j) = true) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ w hw
    left
    unfold V at hw
    simp only [run, List.foldl_nil] at hw
    rcases Nat.lt_or_ge w n with h1 | h1
    · rw [getD_ofFn _ w h1] at hw
      refine ⟨⟨w, h1⟩, hw, ?_⟩
      unfold V
      simp only [run, List.foldl_nil]
      rw [getD_ofFn _ w h1]
      simp [pairInput]
    · rw [List.getD_eq_default _ _ (by simpa using h1)] at hw
      exact absurd hw (by simp)
  | append_singleton gs g ih =>
    intro hall w hw
    have hall' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
      fun g' hg' => hall g' (List.mem_append_left _ hg')
    have hops : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => (hall' g' hg').1
    have ih' := ih hall'
    have hg := hall g (by simp)
    have lift : (∃ j, j < gs.length ∧ (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
        ∃ u v, x u = true ∧ x v = true ∧ V gs (pairInput u v) (n + j) = true) →
        (∃ j, j < (gs ++ [g]).length ∧ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op = GateOp.and ∧
        ∃ u v, x u = true ∧ x v = true ∧ V (gs ++ [g]) (pairInput u v) (n + j) = true) := by
      rintro ⟨j, hj, hop, u, v, hu, hv, hval⟩
      refine ⟨j, by simp; omega, ?_, u, v, hu, hv, ?_⟩
      · rw [List.getD_append _ _ _ _ hj]; exact hop
      · rw [V_snoc, if_pos (by omega)]; exact hval
    rw [V_snoc] at hw
    by_cases h1 : w < n + gs.length
    · rw [if_pos h1] at hw
      rcases ih' w hw with ⟨u, hu, hval⟩ | h2
      · left
        refine ⟨u, hu, ?_⟩
        rw [V_snoc, if_pos h1]; exact hval
      · right; exact lift h2
    · rw [if_neg h1] at hw
      by_cases h2 : w = n + gs.length
      · rw [if_pos h2] at hw
        obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hg.2
        have hnew : ∀ y : Fin n → Bool, V (gs ++ [g]) y w
            = g.op.eval [V gs y a, V gs y b] := by
          intro y
          rw [V_snoc, if_neg h1, if_pos h2, hab]
          rfl
        rw [hab] at hw
        simp only [List.map_cons, List.map_nil] at hw
        rcases hg.1 with hop | hop
        · rw [hop] at hw
          simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true,
            Bool.and_eq_true] at hw
          rcases ih' a hw.1 with ⟨u, hu, hua⟩ | h3
          · rcases ih' b hw.2 with ⟨v, hv, hvb⟩ | h4
            · right
              refine ⟨gs.length, by simp, ?_, u, v, hu, hv, ?_⟩
              · rw [List.getD_append_right _ _ _ _ le_rfl]
                simpa using hop
              · have e := hnew (pairInput u v)
                rw [h2] at e
                rw [e, hop]
                have m1 := V_mono gs hops (pairInput u u) (pairInput u v)
                  (by intro i; simp only [pairInput, decide_eq_true_eq]; tauto) a hua
                have m2 := V_mono gs hops (pairInput v v) (pairInput u v)
                  (by intro i; simp only [pairInput, decide_eq_true_eq]; tauto) b hvb
                simp [GateOp.eval, m1, m2]
            · right; exact lift h4
          · right; exact lift h3
        · rw [hop] at hw
          simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false,
            Bool.or_eq_true] at hw
          rcases hw with hw | hw
          · rcases ih' a hw with ⟨u, hu, hua⟩ | h3
            · left
              refine ⟨u, hu, ?_⟩
              rw [hnew, hop]
              simp [GateOp.eval, hua]
            · right; exact lift h3
          · rcases ih' b hw with ⟨u, hu, hub⟩ | h3
            · left
              refine ⟨u, hu, ?_⟩
              rw [hnew, hop]
              simp [GateOp.eval, hub]
            · right; exact lift h3
      · rw [if_neg h2] at hw
        exact absurd hw (by simp)

def perm {n : ℕ} (f : Fin n → Fin n) (i : ℕ) : ℕ := if h : i < n then (f ⟨i, h⟩).val else i

theorem perm_lt {n : ℕ} (f : Fin n → Fin n) (i : ℕ) (h : i < n) : perm f i < n := by
  unfold perm
  rw [dif_pos h]
  exact (f ⟨i, h⟩).isLt

theorem perm_ge {n : ℕ} (f : Fin n → Fin n) (i : ℕ) (h : n ≤ i) : perm f i = i := by
  unfold perm
  rw [dif_neg (by omega)]

theorem tr {n : ℕ} (f : Fin n → Fin n) (C : Circuit) (x x' : Fin n → Bool)
    (h : ∀ i, x' (f i) = x i) (i : ℕ) :
    ((rc (perm f) C).wires (List.ofFn x')).getD (perm f i) false
      = (C.wires (List.ofFn x)).getD i false := by
  refine ren (perm f) C.gates (List.ofFn x) (List.ofFn x') n (by simp) (by simp) (perm_lt f)
    (perm_ge f) ?_ i
  intro k
  rcases Nat.lt_or_ge k n with h1 | h1
  · rw [getD_ofFn _ _ (perm_lt f k h1), getD_ofFn _ _ h1]
    have e : (⟨perm f k, perm_lt f k h1⟩ : Fin n) = f ⟨k, h1⟩ := by
      apply Fin.ext
      simp [perm, h1]
    rw [e, h]
  · rw [perm_ge f k h1, List.getD_eq_default _ _ (by simpa using h1),
      List.getD_eq_default _ _ (by simpa using h1)]

theorem gateAt_rc (ρ : ℕ → ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (rc ρ C) j = rg ρ (gateAt C j) := by
  unfold gateAt rc
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map]

theorem gf_aut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : G ≃g G)
    (y : Fin n → Bool) : graphFun G ∅ (fun i => y (φ i)) = graphFun G ∅ y := by
  have e : (∃ u v, G.Adj u v ∧ y (φ u) = true ∧ y (φ v) = true)
      ↔ (∃ u v, G.Adj u v ∧ y u = true ∧ y v = true) := by
    constructor
    · rintro ⟨u, v, hadj, hu, hv⟩
      exact ⟨φ u, φ v, φ.map_rel_iff.mpr hadj, hu, hv⟩
    · rintro ⟨u, v, hadj, hu, hv⟩
      refine ⟨φ.symm u, φ.symm v, φ.symm.map_rel_iff.mpr hadj, ?_, ?_⟩
      · simpa using hu
      · simpa using hv
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  exact decide_eq_decide.mpr e

theorem least_rc {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : G ≃g G)
    (C : Circuit) (hC : IsLeastAO G C) : IsLeastAO G (rc (perm φ) C) := by
  obtain ⟨⟨hao, hrb, h2⟩, hfun, hleast⟩ := hC
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [rc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact hao g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [rc] using hj
    rw [gateAt_rc _ C j hj'] at hi
    simp only [rg, List.mem_map] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    have h3 := hrb j hj' a ha
    rcases Nat.lt_or_ge a n with h4 | h4
    · have := perm_lt φ a h4; omega
    · rw [perm_ge φ a h4]; exact h3
  · intro g hg
    simp only [rc, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa [rg] using h2 g0 hg0
  · funext y
    have h1 := tr φ C (fun i => y (φ i)) y (fun i => rfl) C.output
    have h2 : circuitFun n C (fun i => y (φ i)) = graphFun G ∅ (fun i => y (φ i)) := by rw [hfun]
    rw [gf_aut] at h2
    exact h1.trans h2
  · intro C' h1 h2
    have := hleast C' h1 h2
    simpa [rc, Circuit.size] using this

theorem final (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Fin n → Fin n → Prop)
    (H1 : ∀ a b : Fin n, ¬G.Adj a b → ∃ φ : G ≃g G, P (φ a) (φ b))
    (H2 : ∀ C : Circuit, IsLeastAO G C → ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, P a b → gateVal n C j (pairInput a b) = false)
    (C : Circuit) (hC : IsLeastAO G C) : junk G C = ∅ := by
  unfold junk gatesWhere
  rw [Finset.filter_eq_empty_iff]
  intro j _ hd
  obtain ⟨hand, hjlt, x, hx, hF⟩ := hd
  have hall : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hC.1.1 g hg, hC.1.2.2 g hg⟩
  have key : ∃ j', j' < C.gates.length ∧ (gateAt C j').op = GateOp.and ∧
      ∃ u v, x u = true ∧ x v = true ∧ gateVal n C j' (pairInput u v) = true := by
    rcases K x C.gates hall (n + j) hx with ⟨u, hu, hval⟩ | h
    · exact ⟨j, hjlt, hand, u, u, hu, hu, hval⟩
    · exact h
  obtain ⟨j', hj', hand', u, v, hu, hv, hval⟩ := key
  have hnadj : ¬G.Adj u v := by
    intro hadj
    have : graphFun G ∅ x = true := by
      unfold graphFun
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨u, v, hadj, hu, hv⟩
    rw [this] at hF
    exact absurd hF (by simp)
  obtain ⟨φ, hφ⟩ := H1 u v hnadj
  have hC' := least_rc G φ C hC
  have hop' : (gateAt (rc (perm φ) C) j').op = GateOp.and := by
    rw [gateAt_rc _ C j' hj']
    exact hand'
  have h5 := H2 (rc (perm φ) C) hC' j' (by simpa [rc] using hj') hop' (φ u) (φ v) hφ
  have h6 := tr φ C (pairInput u v) (pairInput (φ u) (φ v)) (by intro i; simp [pairInput])
    (n + j')
  rw [perm_ge φ (n + j') (by omega)] at h6
  have h7 : gateVal n (rc (perm φ) C) j' (pairInput (φ u) (φ v)) = true := h6.trans hval
  rw [h7] at h5
  exact absurd h5 (by simp)

end PEqualNP.Outside.L_meta_4057

theorem PEqualNP.Outside.L_meta_4057 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Fin x1 → Fin x1 → Prop), (∀ (x5 x6 : Fin x1), ¬x2.Adj x5 x6 → ∃ (x8 : x2 ≃g x2), x4 (x8 x5) (x8 x6)) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x6 → ∀ x8 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 x12 : Fin x1), x4 x11 x12 → PEqualNP.EdgeOwnership.gateVal x1 x6 x8 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x7 → PEqualNP.TopForm.junk x2 x7 = ∅ := by
  intro n G inst P H1 H2 C hC
  exact L_meta_4057.final n G P H1 H2 C hC
