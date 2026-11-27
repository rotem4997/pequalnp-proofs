import PEqualNP.MetaComplexity.Helpers.EdgeFnOfFront
import PEqualNP.MetaComplexity.Helpers.EdgeFnFront
import PEqualNP.MetaComplexity.Helpers.EdgeFnBaseWin
import PEqualNP.MetaComplexity.Helpers.EdgeFnBaseTP
import PEqualNP.MetaComplexity.Helpers.EdgeFnBaseFront
import PEqualNP.MetaComplexity.Helpers.EdgeFnBaseTwo

/-!
# The extremal choice and the main lemma with the base point (`stmtExt'`, `stmtML'`)

The lemmas of `EdgeFnExt.lean` that take `DeepHyp`, under `DeepHyp'`. `deepHyp_dep'` feeds the
base point to the window in place of the all-false input. `stmtExt'` keeps the conclusion of
`StmtExt'`; its AND branch splits on whether the partner `h` has a second reader: yes, the
exchange as before; no, a gate partner is the stop rule as before, and an input partner is
excluded by the two-point piece `StmtTP`. The other bodies are the old ones verbatim, copied
because the old statements ask for `DeepHyp`.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- A function with `DeepHyp'` on a nonempty `D` is not constant. -/
theorem deepHyp_nc' {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp' F D) (hne : D.Nonempty) : ∃ x y : Fin N → Bool, F x ≠ F y := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, x', h⟩ := hD.nc y hy false
  exact ⟨_, _, h⟩

/-- A function with `DeepHyp'` depends on every input of `D`. -/
theorem deepHyp_dep' {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp' F D) {y : Fin N} (hy : y ∈ D) : Dep F y := by
  obtain ⟨z0, h0⟩ := hD.zeroOn_base
  obtain ⟨x', -, hx'y, hF, hF'⟩ := hD.win y hy _ h0
  refine ⟨x', ?_⟩
  rw [hx'y, hF, show (!false) = true from rfl, hF']
  simp

/-- An OR gate reading a literal of an input `y` of `D` is not below `F`. -/
theorem not_tailOK_or' {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin (n + 1)} {l h : ℕ}
    (hD : DeepHyp' F D) (L : Least (n + 1) F gs o) (hf : Front D gs p g y l h)
    (hop : g.op = GateOp.or) : ¬ TailOK (n + 1) F gs p := by
  obtain ⟨hg, -, hin, hy, hlit, -⟩ := hf
  rintro ⟨g', hg', hop' | ⟨-, hbel⟩⟩
  · rw [hg] at hg'; cases hg'; rw [hop] at hop'; cases hop'
  · rw [hg] at hg'; cases hg'
    -- the value `b` of `y` at which the literal `l` is true
    have key : ∀ b : Bool, (∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = true) → False := by
      intro b hb
      obtain ⟨x, x', hne⟩ := hD.nc y hy b
      have : ∀ z : Fin (n + 1) → Bool, F (Function.update z y b) = true := by
        intro z
        apply hbel
        rw [(vl_bin gs L.hcl _ p l h g hg hin).1 hop, hb _ (by simp)]
        rfl
      exact hne (by rw [this, this])
    rcases hlit with rfl | ⟨pn, rfl, hpn⟩
    · apply key true
      intro x hx
      rw [vl_input gs x y y.isLt]
      simpa using hx
    · apply key false
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn y rfl rfl, vl_input gs x y y.isLt]
      simpa using hx

/-- Piece C10a with the base point, from the pieces C3, C4, C7', C8', C9' and the two-point
piece. -/
theorem stmtExt' (hLift : StmtLift) (hX : StmtXMove) (hFront : StmtFront') (hWin : StmtWin')
    (hTwo : StmtTwo') (hTP : StmtTP) : StmtExt' := by
  classical
  intro n F D s hD hne hs
  have hnc := deepHyp_nc' hD hne
  obtain ⟨gs0, o0, L0, hl0⟩ := exists_least (n + 1) F s hnc hs
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧
    TailGE (n + 1) F gs t
  have hP0 : P 0 := ⟨gs0, o0, L0, TailGE.zero _ _ _⟩
  -- every tail of a least list is at most the common length
  have hbound : ∀ t, P t → t ≤ gs0.length := by
    rintro t ⟨gs, o, L, ht⟩
    exact (least_len L L0) ▸ ht.le
  set M := Nat.findGreatest P gs0.length with hM
  obtain ⟨gs, o, L, ht⟩ : P M := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t, P t → t ≤ M := fun t h => Nat.le_findGreatest (hbound t h) h
  refine ⟨gs, o, L, by rw [least_len L L0]; exact hl0, ?_⟩
  by_contra hstop
  push Not at hstop
  obtain ⟨hone, hnoand⟩ := hstop
  obtain ⟨p, g, y, l, h, hf, hop⟩ := hFront n F D gs o hD hne L hone
  have hw := hWin n F D gs o p g y l h hD L hone hf
  obtain ⟨hg, hor, hin, -, -, -⟩ := id hf
  rcases hor with hand | hor
  · have hbel := hw.2 hand
    by_cases hsec : ∃ t, t ≠ p ∧ Reads gs t h
    · -- the exchange
      obtain ⟨r, g', q, hrp, hg', hand', hin', -⟩ :=
        hTwo n F D gs o p g y l h hD L hone hf hand hsec
      obtain ⟨gs', o', L', ht'⟩ : P (M + 2) := by
        rcases lt_or_gt_of_ne hrp with hlt | hlt
        · obtain ⟨gs', o', L', ht'⟩ :=
            hX (n + 1) F gs o r p q l h g' g L hnc hlt hg' hand' hin' hg hand hin hbel
          exact ⟨gs', o', L', ht' M ht⟩
        · obtain ⟨gs', o', L', ht'⟩ :=
            hX (n + 1) F gs o p r l q h g g' L hnc hlt hg hand hin hg' hand' hin' hbel
          exact ⟨gs', o', L', ht' M ht⟩
      have := hmax _ ⟨gs', o', L', ht'⟩
      omega
    · have honly : ∀ t, Reads gs t h → t = p := fun t ht => by
        by_contra e
        exact hsec ⟨t, e, ht⟩
      by_cases hhN : n + 1 ≤ h
      · -- a gate partner read only by `p`: the stop rule
        obtain ⟨t, htr, htp⟩ := hnoand p g y l h hf hand hhN hop
        exact htp (honly t htr)
      · -- an input partner read only by `p`: the two-point piece
        obtain ⟨-, -, -, hy, hlit, -⟩ := hf
        exact hTP (n + 1) F gs o p g y l h L.hcl L.hev hg hand hin hlit (by omega) honly hbel
          (hD.nc y hy)
  · -- the lift
    have hbel := hw.1 hor
    obtain ⟨L', ht'⟩ := hLift (n + 1) F gs o p l h g L hnc hg hor hin hbel
    have := hmax _ ⟨_, _, L', ht' (not_tailOK_or' hD L hf hor) M ht⟩
    omega

/-- Piece C10b with the base point, from the pieces C6 and C10a', with the checked
`Least.two_readers` and `Least.not_two_readers`. -/
theorem stmtML' (hAnd : StmtAnd) (hExt : StmtExt') : StmtML' := by
  intro n F D s hD hne hs
  have hnc := deepHyp_nc' hD hne
  obtain ⟨gs, o, L, hls, halt⟩ := hExt n F D s hD hne hs
  rcases halt with hone | ⟨p, g, y, l, h, hf, hand, hhN, hop, honly⟩
  · simp only [OneReader, not_and_or] at hone
    push Not at hone
    rcases hone with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · refine ⟨y, hy, ?_⟩
      rcases L.two_readers y (hD.nc y hy) p q hpq hp hq with
        ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
      · exact Or.inl (h3.mono le_rfl hls)
      · exact Or.inl (h4.mono (by omega) hls)
      · exact Or.inr (h4.mono le_rfl hls)
    · refine ⟨y, hy, Or.inl ?_⟩
      exact (L.not_two_readers y (hD.nc y hy) pn _ hpn rfl (by simp) p q hpq hp hq).1.mono
        le_rfl hls
  · obtain ⟨hg, -, hin, hy, hlit, hfree⟩ := hf
    refine ⟨y, hy, ?_⟩
    have hrd : Reads gs p h := ⟨g, hg, by rcases hin with e | e <;> rw [e] <;> simp⟩
    have hhlt := reads_lt L.hcl hrd
    have hplt := reads_len hrd
    have hdep := deepHyp_dep' hD hy
    -- the output is not `h`: the support of `h` avoids `y`, and `F` depends on `y`
    have hoh : o ≠ h := by
      rintro rfl
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← L.hev, ← L.hev]
      exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
        (agree_inputs _ _)).2.2 o (by
          intro k hk
          have : k ≠ y := fun e => hfree y hy (e ▸ hk)
          simp [Function.update_of_ne this])
    obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
    have hA := hAnd n F gs o p ph l g y L (hD.nc y hy) hdep hg hand hin hlit (by omega)
      honly hop hoh
    by_cases hl : l = (y : ℕ)
    · exact Or.inl ((hA.1 hl).mono le_rfl hls)
    · exact Or.inr ((hA.2 hl).mono le_rfl hls)

/-- The main lemma with the base point, all pieces proved. -/
theorem stmtML'_final : StmtML' :=
  stmtML' stmtAnd (stmtExt' stmtLift stmtXMove stmtFront' stmtWin' (stmtTwo' stmtExch stmtWin')
    stmtTP)

end PEqualNP.MetaComplexity.EdgeFn
