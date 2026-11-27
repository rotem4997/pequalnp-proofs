import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.Defs.MetaComplexity

/-!
# Theorem NL, part 1: wire values of a raw gate list

Helper layer for the NOT-state row (`L588.lean`). Everything here is on raw gate lists in the
root's convention: a gate may list any wire; a wire that does not exist yet when the gate is
evaluated reads `false`; a NOT gate looks at its first listed wire only. No cleanliness is
assumed anywhere.

`nlV gs x j` is the value of wire `j` when the gates `gs` run on the input list `x`; it is the
value `Circuit.eval` reads. `nlRel g a` says that gate `g` reads wire `a` in the sense of the
free-input-chain statement: a NOT gate reads its first listed wire, any other gate every listed
wire. The freeness lemma `nl_free` compares the values at two inputs.
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One evaluation step: append the value of gate `g` to the wire list `w`. -/
def nlStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- All wire values of the gate list `gs` on the input list `x`. -/
def nlW (gs : List Gate) (x : List Bool) : List Bool := gs.foldl nlStep x

/-- The value of wire `j`. -/
def nlV (gs : List Gate) (x : List Bool) (j : ℕ) : Bool := (nlW gs x).getD j false

/-- Gate `g` reads wire `a`: a NOT gate its first listed wire, any other gate every listed wire. -/
def nlRel (g : Gate) (a : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨ (g.op ≠ GateOp.not ∧ a ∈ g.inputs)

theorem nl_eval (C : Circuit) (x : List Bool) : C.eval x = nlV C.gates x C.output := rfl

theorem nlW_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    nlW (g :: gs) w = nlW gs (nlStep w g) := rfl

theorem nlW_length (gs : List Gate) : ∀ w : List Bool, (nlW gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [nlW]
  | cons g gs ih =>
    intro w
    rw [nlW_cons, ih]
    simp [nlStep]
    omega

theorem nlW_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (nlW gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [nlW_cons, ih _ i (by simp [nlStep]; omega)]
    simp only [nlStep]
    rw [List.getD_append _ _ _ _ hi]

theorem nlW_append (l1 l2 : List Gate) (w : List Bool) :
    nlW (l1 ++ l2) w = nlW l2 (nlW l1 w) := by
  simp [nlW, List.foldl_append]

theorem nlV_input (gs : List Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    nlV gs x i = x.getD i false := nlW_prefix gs x i h

theorem nlV_past (gs : List Gate) (x : List Bool) (j : ℕ) (h : x.length + gs.length ≤ j) :
    nlV gs x j = false := by
  unfold nlV
  exact List.getD_eq_default _ _ (by rw [nlW_length]; omega)

/-- The value of gate `p`: its operation on its listed wires, each read as its value if it is
an earlier wire and as `false` otherwise. -/
theorem nlV_gate (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length) :
    nlV gs x (x.length + p) = gs[p].op.eval (gs[p].inputs.map fun i =>
      if i < x.length + p then nlV gs x i else false) := by
  have hsplit : gs = gs.take p ++ (gs[p] :: gs.drop (p + 1)) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  set w := nlW (gs.take p) x with hw
  have hwl : w.length = x.length + p := by
    rw [hw, nlW_length, List.length_take]; omega
  have hall : nlW gs x = nlW (gs.drop (p + 1)) (nlStep w gs[p]) := by
    conv_lhs => rw [hsplit]
    rw [nlW_append, nlW_cons]
  have hread : ∀ i, i < x.length + p → nlV gs x i = w.getD i false := by
    intro i hi
    unfold nlV
    rw [hall, nlW_prefix _ _ i (by simp [nlStep]; omega)]
    simp only [nlStep]
    rw [List.getD_append _ _ _ _ (by omega)]
  have hmain : nlV gs x (x.length + p) =
      gs[p].op.eval (gs[p].inputs.map fun i => w.getD i false) := by
    unfold nlV
    rw [hall, nlW_prefix _ _ _ (by simp [nlStep]; omega)]
    simp only [nlStep]
    rw [List.getD_append_right _ _ _ _ (by omega), hwl, Nat.sub_self]
    simp only [List.getD_cons_zero]
  rw [hmain]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + p
  · rw [if_pos hi, hread i hi]
  · rw [if_neg hi]
    exact List.getD_eq_default _ _ (by omega)

/-- A gate's value depends only on the wires it reads. -/
theorem nl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ a, nlRel g a → f a = f' a) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  by_cases hop : g.op = GateOp.not
  · rw [hop]
    cases hl : g.inputs with
    | nil => rfl
    | cons a t =>
      have := h a (Or.inl ⟨hop, by rw [hl]; rfl⟩)
      simp [GateOp.eval, this]
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact h a (Or.inr ⟨hop, ha⟩)

/-- The read of wire `a` by gate `p` of a list on `N` inputs. -/
def nlRd (gs : List Gate) (x : List Bool) (p a : ℕ) : Bool :=
  if a < x.length + p then nlV gs x a else false

theorem nlV_gate' (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length) :
    nlV gs x (x.length + p) = gs[p].op.eval (gs[p].inputs.map (nlRd gs x p)) :=
  nlV_gate gs x p hp

/-- Freeness: wires outside a set `Bad` agree at two inputs, if the inputs outside `Bad` agree
and every gate outside `Bad` reads, among earlier wires, only wires outside `Bad` or wires
already known to agree. -/
theorem nl_free (gs : List Gate) (x y : List Bool) (hl : x.length = y.length) (Bad : ℕ → Prop)
    (hin : ∀ i, i < x.length → ¬ Bad i → x.getD i false = y.getD i false)
    (hg : ∀ (p : ℕ) (hp : p < gs.length), ¬ Bad (x.length + p) → ∀ a, nlRel gs[p] a →
      a < x.length + p → ¬ Bad a ∨ nlV gs x a = nlV gs y a) :
    ∀ w, ¬ Bad w → nlV gs x w = nlV gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwi : w < x.length
    · rw [nlV_input _ _ _ hwi, nlV_input _ _ _ (by omega)]
      exact hin w hwi hw
    · by_cases hwp : x.length + gs.length ≤ w
      · rw [nlV_past _ _ _ hwp, nlV_past _ _ _ (by omega)]
      · obtain ⟨p, rfl⟩ : ∃ p, w = x.length + p := ⟨w - x.length, by omega⟩
        have hp : p < gs.length := by omega
        rw [nlV_gate gs x p hp]
        have := nlV_gate gs y p hp
        rw [← hl] at this
        rw [this]
        apply nl_eval_congr
        intro a ha
        by_cases hal : a < x.length + p
        · rw [if_pos hal, if_pos hal]
          rcases hg p hp hw a ha hal with h | h
          · exact ih a hal h
          · exact h
        · rw [if_neg hal, if_neg hal]

/-! ## Single gates -/

theorem nl_or_true (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length)
    (hop : gs[p].op = GateOp.or) (a : ℕ) (ha : a ∈ gs[p].inputs) (hal : a < x.length + p)
    (hv : nlV gs x a = true) : nlV gs x (x.length + p) = true := by
  rw [nlV_gate gs x p hp, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨a, ha, by rw [if_pos hal, hv]⟩, rfl⟩

theorem nl_or_some (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length)
    (hop : gs[p].op = GateOp.or) (hv : nlV gs x (x.length + p) = true) :
    ∃ a ∈ gs[p].inputs, a < x.length + p ∧ nlV gs x a = true := by
  rw [nlV_gate gs x p hp, hop] at hv
  simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hv
  obtain ⟨b, ⟨a, ha, hab⟩, hb⟩ := hv
  refine ⟨a, ha, ?_⟩
  by_cases hal : a < x.length + p
  · rw [if_pos hal] at hab
    exact ⟨hal, by rw [hab]; exact hb⟩
  · rw [if_neg hal] at hab
    rw [← hab] at hb
    cases hb

theorem nl_and_true (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length)
    (hop : gs[p].op = GateOp.and) (hv : nlV gs x (x.length + p) = true) :
    ∀ a ∈ gs[p].inputs, a < x.length + p ∧ nlV gs x a = true := by
  rw [nlV_gate gs x p hp, hop] at hv
  simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hv
  intro a ha
  have := hv _ ⟨a, ha, rfl⟩
  by_cases hal : a < x.length + p
  · rw [if_pos hal] at this
    exact ⟨hal, this⟩
  · rw [if_neg hal] at this
    cases this

theorem nl_and_false (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length)
    (hop : gs[p].op = GateOp.and) (a : ℕ) (ha : a ∈ gs[p].inputs)
    (hv : a < x.length + p → nlV gs x a = false) : nlV gs x (x.length + p) = false := by
  cases h : nlV gs x (x.length + p) with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := nl_and_true gs x p hp hop h a ha
    rw [hv h1] at h2
    cases h2

theorem nl_not_val (gs : List Gate) (x : List Bool) (p : ℕ) (hp : p < gs.length)
    (hop : gs[p].op = GateOp.not) (a : ℕ) (ha : gs[p].inputs.head? = some a)
    (hal : a < x.length + p) : nlV gs x (x.length + p) = !nlV gs x a := by
  rw [nlV_gate gs x p hp, hop]
  cases hl : gs[p].inputs with
  | nil => rw [hl] at ha; cases ha
  | cons b t =>
    rw [hl] at ha
    simp at ha
    subst ha
    simp [GateOp.eval, hal]

end PEqualNP.MetaComplexity.Helpers.RunNL
