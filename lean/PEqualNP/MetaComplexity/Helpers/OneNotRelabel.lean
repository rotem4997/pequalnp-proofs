import PEqualNP.MetaComplexity.Helpers.OneNotEval

/-!
# One NOT gate: relabel simulation

Step 2 of the build plan (and step 5, the
deletion piece S-PIECE-U, which is an instance). One generic lemma: a gate list whose wire
references are mapped by `r`, run on start wires `v`, has at `r i` the value the original list,
run on start wires `w`, has at `i`, provided `r` is right on the start wires, sends the `k`-th
gate's wire to the `k`-th new gate's wire, and sends every other index to a wire that is either
already present or never exists. Then the three instances: S-RESTRICT-DOWN, S-RESTRICT-UP,
S-PIECE-U.
-/

namespace PEqualNP.MetaComplexity.OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-- A gate with its wire references mapped by `r`. -/
def on1_relabel (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

/-- The generic simulation, with the invariant on every index. -/
theorem on1_relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_relabel r g).op.eval
          ((on1_relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

/-- The generic simulation: it is enough that `r` is right on the start wires. -/
theorem on1_relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

theorem on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

/-- S-RESTRICT-DOWN: inputs outside `a` read as false; same length. -/
theorem on1_restrict_down : ∀ (n : ℕ) (a : Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨gates.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
            PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => x i && decide (i ∈ a))) := by
  intro n a gates
  refine ⟨fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ a then i else n + gates.length)
    else i, ?_⟩
  intro o x
  set r : ℕ → ℕ := fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ a then i else
    n + gates.length) else i with hr
  show (wiresFrom (gates.map (on1_relabel r)) (List.ofFn x)).getD (r o) false
    = (wiresFrom gates (List.ofFn (fun i => x i && decide (i ∈ a)))).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_ofFn] at hi
    rw [on1_getD_ofFn _ _ hi]
    by_cases ha : (⟨i, hi⟩ : Fin n) ∈ a
    · simp [hr, hi, ha]
    · simp only [hr, hi, ha, dite_true, ite_false]
      rw [List.getD_eq_default _ _ (by simp)]; simp
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    by_cases ha : (⟨i, hi⟩ : Fin n) ∈ a
    · left; simp [hr, hi, ha]
    · right; simp [hr, hi, ha]
  · intro k _
    simp [hr]
  · intro i hi
    simp only [List.length_ofFn] at hi ⊢
    simp [hr, show ¬ i < n by omega]; omega

/-- S-RESTRICT-UP: inputs in `b` read as true; one extra gate (AND with no inputs, in front). -/
theorem on1_restrict_up : ∀ (n : ℕ) (b : Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
              PEqualNP.CircuitLowerBounds.Gate) ::
            gates.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
              PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => x i || decide (i ∈ b))) := by
  intro n b gates
  refine ⟨fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ b then n else i) else i + 1, ?_⟩
  intro o x
  set r : ℕ → ℕ := fun i => if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ b then n else i)
    else i + 1 with hr
  have e : (List.ofFn x).getD n false = false := List.getD_eq_default _ _ (by simp)
  show (wiresFrom (gates.map (on1_relabel r)) (List.ofFn x ++ [true])).getD (r o) false
    = (wiresFrom gates (List.ofFn (fun i => x i || decide (i ∈ b)))).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_ofFn] at hi
    rw [on1_getD_ofFn _ _ hi]
    by_cases hb : (⟨i, hi⟩ : Fin n) ∈ b
    · simp only [hr, hi, hb, dite_true, ite_true]
      have := getD_snoc_eq (List.ofFn x) true false
      simp only [List.length_ofFn] at this
      rw [this]; simp
    · simp only [hr, hi, hb, dite_true, ite_false]
      rw [on1_getD_append_left _ _ _ (by simpa using hi), on1_getD_ofFn _ _ hi]; simp
  · intro i hi
    simp only [List.length_ofFn] at hi
    left
    by_cases hb : (⟨i, hi⟩ : Fin n) ∈ b
    · simp [hr, hi, hb]
    · simp [hr, hi, hb]; omega
  · intro k _
    simp [hr]; omega
  · intro i hi
    simp only [List.length_ofFn] at hi
    simp [hr, show ¬ i < n by omega]; omega

end PEqualNP.MetaComplexity.OneNot
