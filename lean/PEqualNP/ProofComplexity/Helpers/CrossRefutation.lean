import PEqualNP.Defs.ProofComplexityLinK

/-!
# The 11-line Res(2, ⊕) refutation of the cross formula

The formula on the variables `x, y, z, w` (`0, 1, 2, 3`) with the clauses `x ∨ y`, `z ∨ w` and
the four clauses `¬a ∨ ¬b` for `a` in `{x, y}`, `b` in `{z, w}`. The refutation: six axioms, two
and-introductions making the term `z = 0 ∧ w = 0`, two cuts on one-equation terms and one cut
on the two-equation term.
-/

namespace PEqualNP.ProofComplexity.Helpers.Cross

open PEqualNP.ProofComplexity

/-- The cross formula. -/
def crossF : Set (Clause (Fin 4)) :=
  {{((0 : Fin 4), true), (1, true)}, {((2 : Fin 4), true), (3, true)}, {((0 : Fin 4), false), (2, false)}, {((0 : Fin 4), false), (3, false)}, {((1 : Fin 4), false), (2, false)}, {((1 : Fin 4), false), (3, false)}}

/-- The equation `v = b`. -/
def e (v : Fin 4) (b : Bool) : LinEq (Fin 4) := ({v}, b)

/-- The term `z = 0 ∧ w = 0`. -/
def zw : LinTerm (Fin 4) := {e 2 false, e 3 false}

def l0 : LinKLine (Fin 4) := {{e 0 true}, {e 1 true}}
def l1 : LinKLine (Fin 4) := {{e 2 true}, {e 3 true}}
def l2 : LinKLine (Fin 4) := {{e 0 false}, {e 2 false}}
def l3 : LinKLine (Fin 4) := {{e 0 false}, {e 3 false}}
def l4 : LinKLine (Fin 4) := {{e 1 false}, {e 2 false}}
def l5 : LinKLine (Fin 4) := {{e 1 false}, {e 3 false}}
def l6 : LinKLine (Fin 4) := {{e 0 false}, zw}
def l7 : LinKLine (Fin 4) := {{e 1 false}, zw}
def l8 : LinKLine (Fin 4) := {{e 1 true}, zw}
def l9 : LinKLine (Fin 4) := {zw}
def l10 : LinKLine (Fin 4) := ∅

/-- The refutation, newest line first. -/
def crossPi : List (LinKLine (Fin 4)) := [l10, l9, l8, l7, l6, l5, l4, l3, l2, l1, l0]

theorem ax0 : l0 ∈ (fun C => linKOfClause C) '' crossF :=
  ⟨{((0 : Fin 4), true), (1, true)}, by simp [crossF], by decide⟩
theorem ax1 : l1 ∈ (fun C => linKOfClause C) '' crossF :=
  ⟨{((2 : Fin 4), true), (3, true)}, by simp [crossF], by decide⟩
theorem ax2 : l2 ∈ (fun C => linKOfClause C) '' crossF :=
  ⟨{((0 : Fin 4), false), (2, false)}, by simp [crossF], by decide⟩
theorem ax3 : l3 ∈ (fun C => linKOfClause C) '' crossF :=
  ⟨{((0 : Fin 4), false), (3, false)}, by simp [crossF], by decide⟩
theorem ax4 : l4 ∈ (fun C => linKOfClause C) '' crossF :=
  ⟨{((1 : Fin 4), false), (2, false)}, by simp [crossF], by decide⟩
theorem ax5 : l5 ∈ (fun C => linKOfClause C) '' crossF :=
  ⟨{((1 : Fin 4), false), (3, false)}, by simp [crossF], by decide⟩

theorem and6 : IsLinKAndIntro l2 l3 l6 := ⟨{e 2 false}, {e 3 false}, by decide, by decide, by decide⟩
theorem and7 : IsLinKAndIntro l4 l5 l7 := ⟨{e 2 false}, {e 3 false}, by decide, by decide, by decide⟩
theorem cut8 : IsLinKCut l0 l6 l8 := ⟨{e 0 true}, by decide, by decide, by decide⟩
theorem cut9 : IsLinKCut l8 l7 l9 := ⟨{e 1 true}, by decide, by decide, by decide⟩
theorem cut10 : IsLinKCut l9 l1 l10 := ⟨zw, by decide, by decide, by decide⟩

theorem cross_refutation : IsLinKRefutation 2 crossF crossPi ∧ crossPi.length = 11 := by
  refine ⟨⟨?_, by decide⟩, rfl⟩
  have d0 := IsLinKDerivation.ax (k := 2) (W := IsLinKWeakening) IsLinKDerivation.nil ax0
    (by decide)
  have d1 := IsLinKDerivation.ax d0 ax1 (by decide)
  have d2 := IsLinKDerivation.ax d1 ax2 (by decide)
  have d3 := IsLinKDerivation.ax d2 ax3 (by decide)
  have d4 := IsLinKDerivation.ax d3 ax4 (by decide)
  have d5 := IsLinKDerivation.ax d4 ax5 (by decide)
  have d6 := IsLinKDerivation.andIntro d5 (C := l2) (D := l3) (by simp) (by simp) and6
    (by decide)
  have d7 := IsLinKDerivation.andIntro d6 (C := l4) (D := l5) (by simp) (by simp) and7
    (by decide)
  have d8 := IsLinKDerivation.cut d7 (C := l0) (D := l6) (by simp) (by simp) cut8 (by decide)
  have d9 := IsLinKDerivation.cut d8 (C := l8) (D := l7) (by simp) (by simp) cut9 (by decide)
  exact IsLinKDerivation.cut d9 (C := l9) (D := l1) (by simp) (by simp) cut10 (by decide)

end PEqualNP.ProofComplexity.Helpers.Cross
