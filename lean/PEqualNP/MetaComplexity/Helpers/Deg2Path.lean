import PEqualNP.MetaComplexity.Helpers.Deg2Api

/-!
# The path lemma D2-05 (helper for L-meta-649, package P1)

A wire true at `e_p` and false at a test input `z_S` has a downward path to `x_p` along which
every wire is true at `e_p` and false at `z_S`.
-/

namespace PEqualNP.MetaComplexity.Deg2.Path

open PEqualNP.MetaComplexity.Deg2

variable {N : ℕ}

theorem isPath_single (D : Dag N) (a : ℕ) : D.IsPath [a] a a := by
  refine ⟨rfl, rfl, ?_⟩
  intro k hk
  simp at hk

theorem isPath_cons (D : Dag N) {f c b : ℕ} {π : List ℕ} (hk : D.Kid f c)
    (hp : D.IsPath π c b) : D.IsPath (f :: π) f b := by
  obtain ⟨hh, hl, hc⟩ := hp
  cases π with
  | nil => simp at hh
  | cons c' π' =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    refine ⟨rfl, ?_, ?_⟩
    · rw [List.getLast?_cons_cons]; exact hl
    · intro k hk'
      cases k with
      | zero => simpa using hk
      | succ k =>
        have := hc k (by simp at hk' ⊢; omega)
        simpa using this

theorem pt_val {p : Fin N} {i : ℕ} (hi : i < N + N) (h : pt p ⟨i, hi⟩ = true) : i = p.val := by
  unfold pt inp at h
  by_cases hN : i < N
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.castAdd N ⟨i, hN⟩ := rfl
    rw [this, Fin.addCases_left] at h
    simp only [Finset.mem_singleton, decide_eq_true_eq] at h
    rw [← h]
  · have : (⟨i, hi⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ := by
      ext; simp; omega
    rw [this, Fin.addCases_right] at h
    simp at h

/-- D2-05. -/
theorem card05_path (I : Fin N → Fin N → Prop) (D : Dag N) (f : ℕ) (p : Fin N)
    (S : Finset (Fin N)) (h1 : D.val (pt p) f = true) (h0 : D.val (testInput I S) f = false) :
    ∃ π, D.IsPath π f p.val ∧
      ∀ v ∈ π, D.val (pt p) v = true ∧ D.val (testInput I S) v = false := by
  induction f using Nat.strong_induction_on with
  | _ f ih =>
    have step : ∀ c, D.Kid f c → D.val (pt p) c = true → D.val (testInput I S) c = false →
        ∃ π, D.IsPath π f p.val ∧
          ∀ v ∈ π, D.val (pt p) v = true ∧ D.val (testInput I S) v = false := by
      intro c hk hc1 hc0
      obtain ⟨_, _, _, hcf⟩ := id hk
      obtain ⟨π, hπ, hv⟩ := ih c hcf hc1 hc0
      refine ⟨f :: π, isPath_cons D hk hπ, ?_⟩
      intro v hv'
      rcases List.mem_cons.1 hv' with rfl | hv'
      · exact ⟨h1, h0⟩
      · exact hv v hv'
    by_cases hi : f < N + N
    · rw [Dag.val, dif_pos hi] at h1
      have := pt_val hi h1
      subst this
      refine ⟨[p.val], isPath_single D _, ?_⟩
      intro v hv
      simp only [List.mem_singleton] at hv
      subst hv
      exact ⟨by rw [Dag.val, dif_pos hi]; exact h1, h0⟩
    · have hga : ∀ g, D.gates[f - (N + N)]? = some g → D.gateAt f = some g := by
        intro g hg; unfold Dag.gateAt; rw [if_pos (by omega)]; exact hg
      rw [Dag.val, dif_neg hi] at h1 h0
      cases hg : D.gates[f - (N + N)]? with
      | none => rw [hg] at h1; simp at h1
      | some g =>
        rw [hg] at h1 h0
        cases g with
        | and a b =>
          dsimp only at h1 h0
          rw [Bool.and_eq_true] at h1
          obtain ⟨ha, hb⟩ := h1
          split_ifs at ha with hax
          split_ifs at hb with hbx
          have hka : D.Kid f a := ⟨_, hga _ hg, by simp [G.kids], hax⟩
          have hkb : D.Kid f b := ⟨_, hga _ hg, by simp [G.kids], hbx⟩
          rw [dif_pos hax, dif_pos hbx, Bool.and_eq_false_iff] at h0
          rcases h0 with h0 | h0
          · exact step a hka ha h0
          · exact step b hkb hb h0
        | or a b =>
          dsimp only at h1 h0
          rw [Bool.or_eq_false_iff] at h0
          obtain ⟨h0a, h0b⟩ := h0
          rw [Bool.or_eq_true] at h1
          rcases h1 with ha | hb
          · split_ifs at ha with hax
            have hka : D.Kid f a := ⟨_, hga _ hg, by simp [G.kids], hax⟩
            rw [dif_pos hax] at h0a
            exact step a hka ha h0a
          · split_ifs at hb with hbx
            have hkb : D.Kid f b := ⟨_, hga _ hg, by simp [G.kids], hbx⟩
            rw [dif_pos hbx] at h0b
            exact step b hkb hb h0b
        | cst v =>
          dsimp only at h1 h0
          rw [h1] at h0
          cases h0

end PEqualNP.MetaComplexity.Deg2.Path
