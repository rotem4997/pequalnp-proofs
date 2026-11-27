import PEqualNP.MetaComplexity.Helpers.RunNL3

/-!
# Theorem NL, part 4: what reaches the NOT state, and the shape forced by two points

`nlE gs N a b`: wire `b` is a gate that reads the earlier wire `a`. Everything reached from input
`ev` is the NOT gate, the AND gate, the OR gate or reached from the OR gate. At two input lists
`X0`, `X1` that differ only at `ev`, where the output is `false` at `X0` and `true` at `X1`:
the output is reached from `ev`, the OR gate reads the AND gate as an earlier wire, and the AND
gate is `true` at `X0` (so it reads only earlier wires).
-/

namespace PEqualNP.MetaComplexity.Helpers.RunNL

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Wire `b` is a gate reading the earlier wire `a`. -/
def nlE (gs : List Gate) (N a b : ℕ) : Prop :=
  ∃ j, j < gs.length ∧ b = N + j ∧ a < b ∧ nlRel (gs.getD j nlG0) a

theorem nlE_lt {gs : List Gate} {N a b : ℕ} (h : Relation.TransGen (nlE gs N) a b) : a < b := by
  induction h with
  | single h => obtain ⟨_, _, _, h, _⟩ := h; exact h
  | tail _ h ih => obtain ⟨_, _, _, h, _⟩ := h; omega

section
variable {n : ℕ} {gs : List Gate} {ev pn pm pS : ℕ}

/-- Everything reached from `ev` is `pn`, `pm`, `pS` or reached from `pS`. -/
theorem nlState.reach (hN : nlState n gs ev pn pm pS) {w : ℕ}
    (h : Relation.TransGen (nlE gs (n + 1)) ev w) :
    w = n + 1 + pn ∨ w = n + 1 + pm ∨ w = n + 1 + pS ∨
      Relation.TransGen (nlE gs (n + 1)) (n + 1 + pS) w := by
  induction h with
  | single h =>
    obtain ⟨j, hj, rfl, _, hr⟩ := h
    exact Or.inl (by rw [hN.rd_e j hj hr])
  | tail _ h ih =>
    obtain ⟨j, hj, rfl, hlt, hr⟩ := h
    rcases ih with rfl | rfl | rfl | ih
    · exact Or.inr (Or.inl (by rw [hN.rd_n j hj hr]))
    · exact Or.inr (Or.inr (Or.inl (by rw [hN.rd_m j hj hr])))
    · exact Or.inr (Or.inr (Or.inr (Relation.TransGen.single ⟨j, hj, rfl, hlt, hr⟩)))
    · exact Or.inr (Or.inr (Or.inr (Relation.TransGen.tail ih ⟨j, hj, rfl, hlt, hr⟩)))

/-- The reach set of `ev`. -/
def nlRch (gs : List Gate) (N ev w : ℕ) : Prop := w = ev ∨ Relation.TransGen (nlE gs N) ev w

/-- Wires outside the reach set of `ev` agree at two inputs that agree off `ev`. -/
theorem nl_free_rch (X Y : List Bool) (hX : X.length = n + 1) (hY : Y.length = n + 1)
    (hag : ∀ i, i < n + 1 → i ≠ ev → X.getD i false = Y.getD i false) :
    ∀ w, ¬ nlRch gs (n + 1) ev w → nlV gs X w = nlV gs Y w := by
  apply nl_free gs X Y (by rw [hX, hY]) (nlRch gs (n + 1) ev)
  · intro i hi hb
    exact hag i (by omega) (fun h => hb (Or.inl h))
  · intro p hp hpb a ha hal
    left
    intro hab
    apply hpb
    right
    have he : nlE gs (n + 1) a (X.length + p) :=
      ⟨p, hp, by rw [hX], hal, by rw [nl_getD hp]; exact ha⟩
    rcases hab with rfl | hab
    · exact Relation.TransGen.single he
    · exact Relation.TransGen.tail hab he

/-! ## Two points -/

variable (o : ℕ) (hN : nlState n gs ev pn pm pS)
  (X0 X1 : List Bool) (hX0 : X0.length = n + 1) (hX1 : X1.length = n + 1)
  (he1 : X1.getD ev false = true)
  (hag : ∀ i, i < n + 1 → i ≠ ev → X0.getD i false = X1.getD i false)
  (hF0 : nlV gs X0 o = false) (hF1 : nlV gs X1 o = true) (hoe : o ≠ ev)
include hN hX0 hX1 he1 hag hF0 hF1 hoe

theorem nl_o_n : o ≠ n + 1 + pn := by
  intro h; rw [h, hN.vn X1 hX1 he1] at hF1; cases hF1

theorem nl_o_m : o ≠ n + 1 + pm := by
  intro h; rw [h, hN.vm X1 hX1 he1] at hF1; cases hF1

/-- The OR gate reads the AND gate as an earlier wire, and the AND gate is `true` at `X0`. -/
theorem nl_shape : pm < pS ∧ nlV gs X0 (n + 1 + pm) = true := by
  by_contra hcon
  have hfree := nl_free gs X0 X1 (by rw [hX0, hX1])
    (fun w => w = ev ∨ w = n + 1 + pn ∨ w = n + 1 + pm)
    (by
      intro i hi hb
      exact hag i (by omega) (fun h => hb (Or.inl h)))
    (by
      intro p hp hpb a ha hal
      rw [← nl_getD hp] at ha
      by_cases hab : a = ev ∨ a = n + 1 + pn ∨ a = n + 1 + pm
      · right
        rcases hab with rfl | rfl | rfl
        · exact absurd (Or.inr (Or.inl (by rw [hX0, hN.rd_e p hp ha]))) hpb
        · exact absurd (Or.inr (Or.inr (by rw [hX0, hN.rd_n p hp ha]))) hpb
        · have hp' := hN.rd_m p hp ha
          subst hp'
          have hlt : pm < p := by omega
          have h0 : nlV gs X0 (n + 1 + pm) = false := by
            cases h : nlV gs X0 (n + 1 + pm) with
            | false => rfl
            | true => exact absurd ⟨hlt, h⟩ hcon
          rw [h0, hN.vm X1 hX1 he1]
      · exact Or.inl hab)
  have := hfree o (by
    rintro (h | h | h)
    · exact hoe h
    · exact nl_o_n o hN X0 X1 hX0 hX1 he1 hag hF0 hF1 hoe h
    · exact nl_o_m o hN X0 X1 hX0 hX1 he1 hag hF0 hF1 hoe h)
  rw [hF0, hF1] at this
  cases this

/-- Every wire listed by the AND gate is earlier. -/
theorem nl_m_lt : ∀ a ∈ (gs.getD pm nlG0).inputs, a < n + 1 + pm := by
  intro a ha
  have h := (nl_shape o hN X0 X1 hX0 hX1 he1 hag hF0 hF1 hoe).2
  have := nl_and_true gs X0 pm hN.pm_lt (by rw [← nl_getD hN.pm_lt]; exact hN.m_op)
    (by rw [hX0]; exact h) a (by rw [← nl_getD hN.pm_lt]; exact ha)
  rw [hX0] at this
  exact this.1

/-- The output is the OR gate or reached from it. -/
theorem nl_o_above : o = n + 1 + pS ∨ Relation.TransGen (nlE gs (n + 1)) (n + 1 + pS) o := by
  by_cases hr : nlRch gs (n + 1) ev o
  · rcases hr with h | h
    · exact absurd h hoe
    · rcases hN.reach h with h | h | h | h
      · exact absurd h (nl_o_n o hN X0 X1 hX0 hX1 he1 hag hF0 hF1 hoe)
      · exact absurd h (nl_o_m o hN X0 X1 hX0 hX1 he1 hag hF0 hF1 hoe)
      · exact Or.inl h
      · exact Or.inr h
  · have := nl_free_rch X0 X1 hX0 hX1 hag o hr
    rw [hF0, hF1] at this
    cases this

end

/-- The other operand of the OR gate is not reached from `ev`. -/
theorem nlState.s_free {n : ℕ} {gs : List Gate} {ev pn pm pS : ℕ}
    (hN : nlState n gs ev pn pm pS) {s : ℕ} (hs : nlSo n gs pm pS = some s) :
    ¬ nlRch gs (n + 1) ev s := by
  obtain ⟨h1, h2, h3⟩ := nlSo_spec n gs pm pS s hs
  rintro (h | h)
  · subst h
    exact hN.nS (hN.rd_e pS hN.pS_lt (hN.rS _ h1)).symm
  · rcases hN.reach h with h | h | h | h
    · subst h; exact hN.mS (hN.rd_n pS hN.pS_lt (hN.rS _ h1)).symm
    · exact h2 h
    · omega
    · have := nlE_lt h; omega

end PEqualNP.MetaComplexity.Helpers.RunNL
