import PEqualNP.MetaComplexity.Helpers.OneNotRelabel

/-!
# One NOT gate: the two pieces

Steps 3, 4 and 5 of the build plan, and the cheap
U piece asked for by the seat: S-PIECE-H (the value the NOT gate reads is monotone when the
gates before it are AND/OR gates), S-PIECE-D (where it reads false, the NOT gate can be
replaced in place by AND of nothing), the cheap U piece (where it reads true, replaced in
place by OR of nothing), and S-PIECE-U (where it reads true, deleted, with a renumbering).
-/

namespace PEqualNP.MetaComplexity.OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-! ## Monotonicity of AND/OR gate lists -/

/-- `v'` is above `v` wire by wire (as read with `getD`), with the same length. -/
def on1_Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

theorem on1_above_snoc {v v' : List Bool} {a a' : Bool} (h : on1_Above v v')
    (ha : a = true → a' = true) : on1_Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]; exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

theorem on1_above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, on1_Above v v' → on1_Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply on1_above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

/-- S-PIECE-H: the value the NOT gate reads is monotone in the input. -/
theorem on1_piece_h : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
    (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn y)).getD i false).headD false) = true := by
  intro n pre ins hpre x y hxy
  have hab : on1_Above (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn y)) := by
    apply on1_above_wiresFrom pre (fun g hg => (hpre g hg).1)
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  cases ins with
  | nil => simp
  | cons j _ =>
    simp only [List.map_cons, List.headD_cons]
    exact hab.2 j

/-! ## Changing one slot -/

/-- Two gate lists that differ only at one slot have equal wires once the two slot gates give
the same value on the wires before the slot. -/
theorem on1_wires_slot (pre post : List Gate) (g g' : Gate) (o o' : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)) :
    Circuit.wires ⟨pre ++ g :: post, o⟩ x = Circuit.wires ⟨pre ++ g' :: post, o'⟩ x := by
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o' 0, on1_wiresFrom_cons,
    on1_wiresFrom_cons, h]

/-- S-PIECE-D: where the NOT gate reads false, it can be replaced in place by AND of nothing. -/
theorem on1_piece_d : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.all_nil]
  rw [h]; rfl

/-- The cheap U piece: where the NOT gate reads true, it can be replaced in place by OR of
nothing (same length; no renumbering). -/
theorem on1_piece_u_cheap : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  rw [h]; rfl

/-! ## Deletion with renumbering -/

/-- S-PIECE-U: where the NOT gate reads true, it can be deleted: one renumbering `r` of the
wires makes (gates before it, then the gates after it renumbered) give at `r o` the value of
the original at `o`, for every `o`. -/
theorem on1_piece_u : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨pre ++ post.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
            PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
            PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins
  set p := pre.length
  refine ⟨fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1, ?_⟩
  intro o x h
  set r : ℕ → ℕ := fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1 with hr
  set v := wiresFrom pre (List.ofFn x) with hv
  have hvl : v.length = n + p := by rw [hv, length_wiresFrom]; simp [p]
  set nv := GateOp.not.eval (ins.map fun i => v.getD i false) with hnv
  have hnv0 : nv = false := by
    rw [hnv]; simp only [GateOp.eval]; rw [show v = Circuit.wires ⟨pre, 0⟩ (List.ofFn x) from rfl,
      h]; rfl
  unfold Circuit.eval
  rw [List.append_cons, on1_wires_append _ _ _ 0, on1_wires_append _ _ _ 0,
    on1_wires_append _ _ _ 0]
  show (wiresFrom (post.map (on1_relabel r)) v).getD (r o) false
    = (wiresFrom post (v ++ [nv])).getD o false
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi
    by_cases hlt : i < n + p
    · simp only [hr, hlt, ite_true]
      rw [on1_getD_append_left _ _ _ (by omega)]
    · have hi' : i = n + p := by omega
      subst hi'
      simp only [hr, lt_irrefl, ite_false, ite_true]
      rw [List.getD_eq_default _ _ (by omega), ← hvl, getD_snoc_eq, hnv0]
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    by_cases hlt : i < n + p
    · left; simp [hr, hlt]
    · right; have hi' : i = n + p := by omega
      subst hi'; simp [hr]
  · intro k _
    simp only [List.length_append, List.length_singleton, hvl, hr]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    simp only [hr]
    split_ifs <;> omega

end PEqualNP.MetaComplexity.OneNot
