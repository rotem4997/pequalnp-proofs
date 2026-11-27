import PEqualNP.MetaComplexity.Helpers.EdgeFnBase
import PEqualNP.MetaComplexity.Helpers.EdgeFnExt

/-!
# The two-point piece (`stmtTP`)

An AND gate `p` reading a literal `l` of `y` and an input wire `h` that nothing else reads
cannot occur when `F` is true wherever `h` is false and both restrictions of `F` at `y` are not
constant. Proof: let `b` be the value of `y` that makes the literal false; a point `u` with
`u y = b` and `F u = false` has `h` true; flipping `h` to false makes `F` true, but only gate `p`
reads `h`, and gate `p` is false at both points, so every wire not `h` agrees, the output among
them (`agree_B`). Minimality of the list is not used.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

theorem stmtTP : StmtTP := by
  intro N F gs o p g y l h hcl hev hgp hand hin hlit hhN hone hbel hnc
  -- the value of `y` at which the literal is false
  obtain ⟨b, hlb⟩ : ∃ b : Bool, ∀ x : Fin N → Bool, x y = b → vl gs x l = false := by
    rcases hlit with e | ⟨pn, e, hpn⟩
    · exact ⟨false, fun x hx => by rw [e, vl_input gs x y y.isLt]; simpa using hx⟩
    · exact ⟨true, fun x hx => by
        rw [e, vl_not gs hcl x pn _ hpn y rfl rfl, vl_input gs x y y.isLt]; simp [hx]⟩
  -- a point with `y = b` where `F` is false
  obtain ⟨u, huy, hFu⟩ : ∃ u : Fin N → Bool, u y = b ∧ F u = false := by
    obtain ⟨x, x', hne⟩ := hnc b
    cases e1 : F (Function.update x y b) with
    | false => exact ⟨_, by simp, e1⟩
    | true =>
      cases e2 : F (Function.update x' y b) with
      | false => exact ⟨_, by simp, e2⟩
      | true => exact absurd (e1.trans e2.symm) hne
  set hi : Fin N := ⟨h, hhN⟩ with hhi
  have hvh : ∀ x : Fin N → Bool, vl gs x h = x hi := fun x => vl_input gs x h hhN
  have huh : u hi = true := by
    cases e : u hi with
    | true => rfl
    | false => rw [hbel u (by rw [hvh, e])] at hFu; cases hFu
  -- `h` is not `y`
  have hhy : hi ≠ y := by
    intro e
    rcases hlit with el | ⟨pn, el, hpn⟩
    · have := hlb u huy
      rw [el, vl_input gs u y y.isLt, ← e, huh] at this
      cases this
    · have hr : Reads gs pn h := ⟨_, hpn, by
        have : (y : ℕ) = h := by rw [← e]
        simp [this]⟩
      have hpe := hone pn hr
      subst hpe
      rw [hpn] at hgp
      cases hgp
      exact GateOp.noConfusion hand
  set u' := Function.update u hi false with hu'
  have hFu' : F u' = true := hbel u' (by rw [hvh, hu']; simp)
  have hu'y : u' y = b := by rw [hu', Function.update_of_ne hhy.symm]; exact huy
  have hoh : o ≠ h := by
    intro e
    have := hev u
    rw [e, hvh, huh, hFu] at this
    cases this
  have key := agree_B gs hcl u u' (fun j => j = h) (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj, hu']
      have hne : (⟨j, hj⟩ : Fin N) ≠ hi := fun e => hB (by rw [hhi] at e; exact Fin.mk.inj e)
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ _ hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hqp : q = p := hone q ⟨g', hq, hBa ▸ ha⟩
      subst hqp
      rw [(vl_bin gs hcl u q l h g hgp hin).2 hand, (vl_bin gs hcl u' q l h g hgp hin).2 hand,
        hlb u huy, hlb u' hu'y]
      rfl)
    o (by omega) hoh
  rw [hev, hev, hFu, hFu'] at key
  cases key

end PEqualNP.MetaComplexity.EdgeFn
