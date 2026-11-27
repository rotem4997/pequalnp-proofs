import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9014

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

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]


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


theorem gv {n : ℕ} (φ : Fin n → Fin n) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n (rc (perm φ) C) j x = gateVal n C j (fun i => x (φ i)) := by
  have h := tr φ C (fun i => x (φ i)) x (fun i => rfl) (n + j)
  rw [perm_ge φ (n + j) (by omega)] at h
  exact h

theorem below_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : G ≃g G)
    (C : Circuit) (j : ℕ) : BelowF G (rc (perm φ) C) j ↔ BelowF G C j := by
  constructor
  · intro h x hx
    have e : (fun i => (fun k => x (φ.symm k)) (φ i)) = x := by
      funext i; simp
    have h1 := h (fun k => x (φ.symm k)) (by rw [gv, e]; exact hx)
    rw [← gf_aut G φ, e] at h1
    exact h1
  · intro h x hx
    rw [gv] at hx
    have h1 := h _ hx
    rw [gf_aut] at h1
    exact h1

theorem dirty_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (φ : G ≃g G)
    (C : Circuit) (j : ℕ) : IsDirty n G (rc (perm φ) C) j ↔ IsDirty n G C j := by
  have hl : (rc (perm φ) C).gates.length = C.gates.length := by simp [rc]
  unfold IsDirty
  rw [hl]
  constructor
  · rintro ⟨hj, x, hx, hF⟩
    refine ⟨hj, fun i => x (φ i), ?_, ?_⟩
    · rw [← gv]; exact hx
    · rw [gf_aut]; exact hF
  · rintro ⟨hj, x, hx, hF⟩
    have e : (fun i => (fun k => x (φ.symm k)) (φ i)) = x := by
      funext i; simp
    refine ⟨hj, fun k => x (φ.symm k), ?_, ?_⟩
    · rw [gv, e]; exact hx
    · rw [← gf_aut G φ, e]; exact hF

theorem filt (ρ : ℕ → ℕ) (n : ℕ) (hlt : ∀ i < n, ρ i < n) (hge : ∀ i, n ≤ i → ρ i = i)
    (k : ℕ) : ∀ l : List ℕ, (l.map ρ).filter (fun w => decide (n ≤ w ∧ w < k))
      = l.filter (fun w => decide (n ≤ w ∧ w < k)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases Nat.lt_or_ge a n with h | h
    · have h2 := hlt a h
      simp only [List.map_cons, List.filter_cons, ih]
      simp [show ¬ n ≤ ρ a by omega, show ¬ n ≤ a by omega]
    · simp only [List.map_cons, List.filter_cons, ih, hge a h]

theorem cones_rc (ρ : ℕ → ℕ) (n : ℕ) (hlt : ∀ i < n, ρ i < n) (hge : ∀ i, n ≤ i → ρ i = i)
    (gs : List Gate) : ∀ cs : List (List ℕ),
      (gs.map (rg ρ)).foldl (coneStep n) cs = gs.foldl (coneStep n) cs := by
  induction gs with
  | nil => intro cs; rfl
  | cons g gs ih =>
    intro cs
    simp only [List.map_cons, List.foldl_cons]
    have : coneStep n cs (rg ρ g) = coneStep n cs g := by
      unfold coneStep rg
      simp only
      rw [filt ρ n hlt hge]
    rw [this, ih]

theorem incone_iff {n : ℕ} (φ : Fin n → Fin n) (C : Circuit) (i j : ℕ) :
    InCone n (rc (perm φ) C) i j ↔ InCone n C i j := by
  unfold InCone cones
  rw [show (rc (perm φ) C).gates = C.gates.map (rg (perm φ)) from rfl,
    cones_rc (perm φ) n (perm_lt φ) (perm_ge φ)]

theorem main (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (φ : G ≃g G) (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) :
    ∃ D : Circuit, D.size = C.size ∧ IsLeastAO G D ∧ TopForm G D ∧ junk G D = junk G C ∧
      ∀ a b : Fin 26, (gateAt C 0).inputs = [↑a, ↑b] →
        (gateAt D 0).inputs = [↑(φ a), ↑(φ b)] := by
  have hl : (rc (perm φ) C).gates.length = C.gates.length := by simp [rc]
  refine ⟨rc (perm φ) C, by simp [rc, Circuit.size], least_rc G φ C hL, ?_, ?_, ?_⟩
  · intro i hi j hj hai hbi haj hc
    rw [hl] at hi hj
    rw [gateAt_rc _ C i hi] at hai
    rw [gateAt_rc _ C j hj] at haj
    rw [below_iff] at hbi
    rw [incone_iff] at hc
    exact hT i hi j hj hai hbi haj hc
  · unfold junk gatesWhere
    rw [hl]
    apply Finset.filter_congr
    intro j hj
    have hj' : j < C.gates.length := Finset.mem_range.mp hj
    unfold IsDirtyAnd
    rw [gateAt_rc _ C j hj', dirty_iff]
    rfl
  · intro a b hab
    have h0 : 0 < C.gates.length := by
      rcases Nat.eq_zero_or_pos C.gates.length with h | h
      · have : C.gates = [] := List.eq_nil_of_length_eq_zero h
        simp [gateAt, this] at hab
      · exact h
    rw [gateAt_rc _ C 0 h0]
    simp only [rg, hab, List.map_cons, List.map_nil]
    simp [perm]

end PEqualNP.Outside.L_meta_9014

theorem PEqualNP.Outside.L_meta_9014 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : x1 ≃g x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → PEqualNP.TopForm.TopForm x1 x4 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x7.size = x4.size ∧ PEqualNP.TopForm.IsLeastAO x1 x7 ∧ PEqualNP.TopForm.TopForm x1 x7 ∧ PEqualNP.TopForm.junk x1 x7 = PEqualNP.TopForm.junk x1 x4 ∧ ∀ (x8 x9 : Fin (26 : ℕ)), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (0 : ℕ)).inputs = [↑x8, ↑x9] → (PEqualNP.MetaComplexity.NestedCover.gateAt x7 (0 : ℕ)).inputs = [↑(x3 x8), ↑(x3 x9)] := by
  intro G d φ C hL hT
  exact PEqualNP.Outside.L_meta_9014.main G φ C hL hT
