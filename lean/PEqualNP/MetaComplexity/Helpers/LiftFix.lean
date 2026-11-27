import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Lift

/-!
# Helpers for L-meta-2715 (the implicant lift iterated to a fixed point)

* `foldl_set_equiv`: replacing a gate by one with the same value on every wire list keeps the
  wires.
* `del n k u E`: delete gate `k` of `E`, redirecting every read of wire `n + k` to `u` and
  shifting every wire above it down by one. If gate `k` always equals wire `u` (`u < n + k`),
  the function is kept (`del_fun`).
-/

namespace PEqualNP.MetaComplexity.LiftFix

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Lift
open PEqualNP.MetaComplexity.NestedCover

/-! ## Replacing a gate by an equivalent one -/

theorem foldl_set_equiv (gs : List Gate) (k : ℕ) (g g' : Gate) (hg : gs[k]? = some g)
    (heq : ∀ w : List Bool, g'.op.eval (g'.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false)) (w0 : List Bool) :
    (gs.set k g').foldl step w0 = gs.foldl step w0 := by
  induction gs generalizing k w0 with
  | nil => simp
  | cons h gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      simp only [List.set_cons_zero, List.foldl_cons]
      congr 1
      unfold step
      rw [heq]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      simp only [List.set_cons_succ, List.foldl_cons]
      exact ih k hg _

/-! ## The value of a gate -/

theorem foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

theorem take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega

/-- A gate `OR [u]` at position `k` has the value of wire `u`. -/
theorem wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
    (w0 : List Bool) (hu : u < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false = (F.wires w0).getD u false := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega), foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl, getD_append_singleton_last, getD_append_left _ _ _ (by omega)]
  simp [GateOp.eval]

/-! ## Deleting a copy gate -/

/-- The wire renaming of a deletion of wire `m`, whose reads go to `u`. -/
def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1

/-- A gate with its reads renamed. -/
def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩

/-- The gate renaming of a deletion of gate `k`. -/
def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1

/-- Delete gate `k` of `E`, redirecting its reads to `u`. -/
def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

theorem sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega

/-- The simulation relation between the old wire list `a` and the new one `b`. -/
def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

theorem getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
    Rel m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  set v := g.op.eval (g.inputs.map fun i => a.getD i false)
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

theorem rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

theorem rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

theorem del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    circuitFun n (del n k u E) = circuitFun n E := by
  funext x
  have hc := hcopy x
  unfold circuitFun Circuit.eval
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)
  -- the value of gate k equals that of u
  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 E.output

theorem del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, if_pos hk]
  omega

theorem del_get (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate) (hj : j ≠ k)
    (h : E.gates[j]? = some g) : (del n k u E).gates[sg k j]? = some (rd (n + k) u g) := by
  by_cases h1 : j < k
  · simp only [del, sg, if_pos h1, List.getElem?_map, List.getElem?_eraseIdx, h]; rfl
  · have h2 : ¬ (j - 1 < k) := by omega
    have h3 : j - 1 + 1 = j := by omega
    simp only [del, sg, if_neg h1, List.getElem?_map, List.getElem?_eraseIdx, if_neg h2, h3, h]
    rfl

theorem del_get_inv (n k u : ℕ) (E : Circuit) (j : ℕ) (g : Gate)
    (h : (del n k u E).gates[j]? = some g) :
    ∃ g0, E.gates[if j < k then j else j + 1]? = some g0 ∧ g = rd (n + k) u g0 := by
  simp only [del, List.getElem?_map, List.getElem?_eraseIdx] at h
  split_ifs at h ⊢ with h1
  · cases hh : E.gates[j]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩
  · cases hh : E.gates[j + 1]? with
    | none => rw [hh] at h; simp at h
    | some g0 => rw [hh] at h; simp at h; exact ⟨g0, rfl, h.symm⟩

theorem del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

theorem gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

theorem readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)

theorem del_readsBack (n k u : ℕ) (E : Circuit) (hE : ReadsBack n E) (hu : u < n + k) :
    ReadsBack n (del n k u E) := by
  apply readsBack_of_get
  intro j g hg
  obtain ⟨g0, hg0, rfl⟩ := del_get_inv n k u E j g hg
  have hr := readsBack_get n E hE _ g0 hg0
  intro i hi
  simp only [rd, List.mem_map] at hi
  obtain ⟨i0, hi0, rfl⟩ := hi
  have := hr i0 hi0
  unfold sig
  split_ifs at this ⊢ <;> omega

theorem readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

end PEqualNP.MetaComplexity.LiftFix
