import PEqualNP.Library.Helpers.OracleCompose
import PEqualNP.Library.Machines.FilterMap

/-!
# L-lib-069: P^A is contained in NP^A

The verifier ignores the witness: on `encodePair (x, w)` it keeps the `inl` symbols, which spell
`x` (`Machines/FilterMap.lean`), then runs the oracle machine deciding `S` on them
(`Helpers/OracleCompose.lean`). The witness bound is `0`.
-/

namespace PEqualNP.Library

open Turing PEqualNP.Library.Machines

theorem L069 : ∀ A : Language Bool, PEqualNP.Library.OracleP A ⊆ PEqualNP.Library.OracleNP A := by
  intro A S hS
  let φ0 : Bool ⊕ Bool → Option Bool := Sum.elim some (fun _ => none)
  have hd : (some true : Option Bool) = none → ∀ x, φ0 x = none := by simp
  have hfm : ∀ l : List (Bool ⊕ Bool),
      (flip bind (TM2.step (fm φ0 (some true)).m))^[l.length + 1 + (l.length + 1)]
          (some (initList (fm φ0 (some true)) l)) =
        some (haltList (fm φ0 (some true)) (l.filterMap φ0)) :=
    fun l => fm_run φ0 (some true) hd l
  have hx : ∀ x w : List Bool, (encodePair (x, w)).filterMap φ0 = x := by
    intro x w
    simp only [encodePair, List.filterMap_append, List.filterMap_map]
    have h1 : (φ0 ∘ Sum.inl) = some := rfl
    have h2 : (φ0 ∘ Sum.inr) = fun _ => none := rfl
    rw [h1, h2]
    simp
  refine ⟨{p | p.1 ∈ S}, 0, ?_, ?_⟩
  · refine Helpers.OracleCompose.ocomp_decides A encodePair _ S Prod.fst (fun _ => Iff.rfl)
      (fm φ0 (some true)) (Equiv.refl _) (Equiv.refl Bool)
      (Polynomial.C 2 * Polynomial.X + Polynomial.C 2) (fun p => ?_) hS
    obtain ⟨x, w⟩ := p
    refine ⟨(encodePair (x, w)).length + 1 + ((encodePair (x, w)).length + 1), ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega
    · have := hfm (encodePair (x, w))
      erw [hx x w] at this
      have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).symm l = l :=
        fun γ l => by simp
      exact (congrArg (fun l => (flip bind (TM2.step (fm φ0 (some true)).m))^[_]
        (some (initList (fm φ0 (some true)) l))) (hm _ _)).trans
        (this.trans (congrArg (fun l => some (haltList (fm φ0 (some true)) l)) (hm Bool x).symm))
  · intro x
    constructor
    · intro hx
      exact ⟨[], by simp, hx⟩
    · rintro ⟨w, -, hw⟩
      exact hw

end PEqualNP.Library
