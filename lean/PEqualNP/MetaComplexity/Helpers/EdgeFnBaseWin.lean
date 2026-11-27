import PEqualNP.MetaComplexity.Helpers.EdgeFnBase
import PEqualNP.MetaComplexity.Helpers.EdgeFnWin

/-!
# The window at a frontier gate with the base point (`stmtWin'`)

`win_core'` is `win_core` of `EdgeFnWin.lean` under `DeepHyp'`: the body is the old one
verbatim (it never used H5); it is copied because the old statement asks for `DeepHyp`, which
`DeepHyp'` does not give. `stmtWin'` drops the gate conjunct of the AND half.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-- `win_core` with the base point (body unchanged). -/
theorem win_core' {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)} {gs : List Gate}
    {o p : ℕ} {g : Gate} {y : Fin N} {l h : ℕ} (H : DeepHyp' F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (hO : OneReader D gs)
    (hF : Front D gs p g y l h) : ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  intro x hx
  cases hFx : F x with
  | true => rfl
  | false =>
  exfalso
  have hz : F (zeroOn D x) = false := by
    cases e : F (zeroOn D x) with
    | false => rfl
    | true => rw [H.mono x e] at hFx; cases hFx
  obtain ⟨x', hx'D, _, hF0, hF1⟩ := H.win y hy x hz
  have hagr : ∀ i, i ∉ D → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hx'D i hi]
  have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hx'D i hi).symm
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (N + p) = fixBit g :=
    vl_abs gs hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr']; exact hx)
  have hc2 : vl gs (Function.update x' y true) (N + p) = fixBit g :=
    vl_abs gs hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr]; exact hx)
  have hol : o ≠ l := out_ne_lit hcl hev y (H.nc y hy) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit hcl hev y (H.nc y hy) y (Or.inl rfl)
  have key := agree_B gs hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin N) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ hBq hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by
            rcases hBa with e | e
            · exact e
            · rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            apply hBq
            right
            rw [el, hq']
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads)
              ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [hev, hev, hF0, hF1] at key
  cases key

/-- Piece C9 with the base point. -/
theorem stmtWin' : StmtWin' := by
  intro n F D gs o p g y l h H L hO hF
  have core := win_core' H L.hcl L.hev hO hF
  exact ⟨fun e x hx => core x (by simp [fixBit, e, hx]),
    fun e x hx => core x (by simp [fixBit, e, hx])⟩

end PEqualNP.MetaComplexity.EdgeFn
