import PEqualNP.MetaComplexity.Helpers.EdgeFnPlan

/-!
# Piece C7 of the edge function plan: the two-reader shape (`stmtTwo`)

At an AND frontier gate `p` of a least list whose partner `h` has a second reader: exactly one
other position reads `h`, and it is an AND gate reading `h`. Proved from piece C5 (`StmtExch`,
the strict exchange count) and piece C9 (`StmtWin`, which gives the cover hypothesis of the
exchange and that `h` is a gate wire), as in `notes/fullproof/plan.md` (P-TWO).

Proof. Leastness and the exchange give `T.card ≤ 2` for every admissible `T`. Three readers of
`h` are such a `T`. A second reader `r` holding an OR or a NOT gate is not the output (OR: `F`
would be constant true; NOT: `F = !h`, but `h` does not depend on `y` while the window makes
`F` depend on `y`), so a later position `t` reads gate `r`; `t ≠ p`, and `{p, r, t}` is
admissible. So gate `r` is an AND gate.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- A wire whose support avoids `y` has the same value at two inputs that differ only at `y`. -/
theorem vl_update_of_not_supp {N : ℕ} (gs : List Gate) (h : ℕ) (y : Fin N)
    (hy : y ∉ (suppsFrom gs (inputSupps N)).getD h ∅) (x : Fin N → Bool) (b : Bool) :
    vl gs (Function.update x y b) h = vl gs x h := by
  have A := agree_wiresFrom (Function.update x y b) x gs _ _ _
    (agree_inputs (Function.update x y b) x)
  refine A.2.2 h ?_
  intro i hi
  have hiy : i ≠ y := fun e => hy (e ▸ hi)
  exact Function.update_of_ne hiy b x

theorem stmtTwo : StmtExch → StmtWin → StmtTwo := by
  intro hEx hWin n F D gs o p g y l h hD L hOne hF hand hsec
  obtain ⟨hgp, _, hin, hyD, hlit, hfree⟩ := hF
  have hcl := L.hcl
  -- F is not constant
  have hnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', hx⟩ := hD.nc y hyD false
    exact ⟨_, _, hx⟩
  obtain ⟨-, hW⟩ := hWin n F D gs o p g y l h hD L hOne ⟨hgp, Or.inl hand, hin, hyD, hlit, hfree⟩
  obtain ⟨hcov, hhN⟩ := hW hand
  -- every admissible T has at most two elements
  have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
      T.card ≤ 2 := by
    intro T hTm
    obtain ⟨gs', o', hc', he', hlen⟩ := hEx (n + 1) F gs o h T hcl L.hev hnc hcov hTm
    have := L.hmin gs' o' hc' he'
    omega
  have hpread : Reads gs p h := ⟨g, hgp, by rcases hin with e | e <;> rw [e] <;> simp⟩
  obtain ⟨r, hrp, hrr⟩ := hsec
  -- every reader of h is p or r
  have hall : ∀ t, Reads gs t h → t = p ∨ t = r := by
    intro t ht
    by_contra hne
    push_neg at hne
    have := hT {p, r, t} (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl hpread
      · exact Or.inl hrr
      · exact Or.inl ht)
    rw [Finset.card_insert_of_notMem (by simp [hrp.symm, hne.1.symm]),
      Finset.card_insert_of_notMem (by simp [hne.2.symm]), Finset.card_singleton] at this
    omega
  obtain ⟨gr, hgr, hhr⟩ := hrr
  have hrlen : r < gs.length := (List.getElem?_eq_some_iff.1 hgr).1
  have hhlt : h < n + 1 + r := reads_lt hcl ⟨gr, hgr, hhr⟩
  rcases hcl r gr hgr with ⟨hnot, j, _, hjin⟩ | ⟨hop, j, k, _, _, hjk⟩
  · -- gate r is `not [h]`: impossible
    exfalso
    have hj : j = h := by rw [hjin] at hhr; simp at hhr; exact hhr.symm
    rw [hj] at hjin
    by_cases ho : o = n + 1 + r
    · -- F = !h, but h does not depend on y and F does
      have h0 : F (zeroOn D (fun _ => false)) = false := by
        have : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
          funext i; simp [zeroOn]
        rw [this]; exact hD.zero
      obtain ⟨x', _, hx'y, hFx', hFx''⟩ := hD.win y hyD _ h0
      have e1 := L.hev x'
      have e2 := L.hev (Function.update x' y true)
      rw [ho, vl_not gs hcl _ r gr hgr h hnot hjin] at e1 e2
      rw [vl_update_of_not_supp gs h y (hfree y hyD) x' true] at e2
      have : F x' = F (Function.update x' y true) := by rw [← e1, ← e2]
      rw [this, hFx''] at hFx'
      exact Bool.noConfusion hFx'
    · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
      have htp : t ≠ p := by
        rintro rfl
        obtain ⟨g2, hg2, hmem⟩ := htr
        have := gate_eq hgp hg2 rfl
        subst this
        have hm : n + 1 + r = l ∨ n + 1 + r = h := by
          rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
        rcases hm with e | e
        · rcases hlit with e' | ⟨pn, e', hpn⟩
          · have := y.isLt; omega
          · have hrpn : r = pn := by omega
            subst hrpn
            have := gate_eq hgr hpn rfl
            rw [this] at hjin
            simp at hjin
            have := y.isLt; omega
        · omega
      have := hT {p, r, t} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inr hnot, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
      omega
  · rcases hop with hop | hop
    · -- gate r is an AND gate reading h
      refine ⟨r, gr, (if j = h then k else j), hrp, hgr, hop, ?_, hall⟩
      rw [hjk] at hhr ⊢
      by_cases hjh : j = h
      · subst hjh; right; simp
      · left
        simp at hhr ⊢
        omega
    · -- gate r is an OR gate reading h: impossible
      exfalso
      by_cases ho : o = n + 1 + r
      · -- F would be constant true
        apply hnc.elim
        intro x hx
        obtain ⟨x', hxx'⟩ := hx
        have key : ∀ z : Fin (n + 1) → Bool, F z = true := by
          intro z
          cases hz : vl gs z h
          · exact hcov z hz
          · rw [← L.hev z, ho, vl_gate gs hcl z r gr hgr, hop, hjk]
            rw [hjk] at hhr
            simp at hhr
            rcases hhr with e | e <;> subst e <;> simp [GateOp.eval, hz]
        exact hxx' (by rw [key x, key x'])
      · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
        have htp : t ≠ p := by
          rintro rfl
          obtain ⟨g2, hg2, hmem⟩ := htr
          have := gate_eq hgp hg2 rfl
          subst this
          have hm : n + 1 + r = l ∨ n + 1 + r = h := by
            rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
          rcases hm with e | e
          · rcases hlit with e' | ⟨pn, e', hpn⟩
            · have := y.isLt; omega
            · have hrpn : r = pn := by omega
              subst hrpn
              have := gate_eq hgr hpn rfl
              rw [this] at hop
              exact GateOp.noConfusion hop
          · omega
        have := hT {p, r, t} (by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact Or.inl hpread
          · exact Or.inl ⟨gr, hgr, hhr⟩
          · exact Or.inr ⟨r, gr, hgr, Or.inl hop, ⟨gr, hgr, hhr⟩, htr⟩)
        rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
        omega

end PEqualNP.MetaComplexity.EdgeFn
