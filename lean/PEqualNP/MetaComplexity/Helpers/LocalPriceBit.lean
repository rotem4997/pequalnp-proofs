import PEqualNP.MetaComplexity.Helpers.Chain016

/-!
# The bit language of a polynomial-time table producer

Helper module (proofs only, no statement may use it). The machine half of the uniform price of
a local reduction (`LocalPrice.price_uniform` takes the statement proved here as a hypothesis;
the two modules sit on the two sides of the `Counting` / `Columns` import clash).

For a polynomial-time map `r` and an exponent `k`, one language in EXP answers, on the input
`i ++ c` with `c` a code of `x` of length `2 |x| + 1`, whether entry `i` of the partial table
written by `r` on the exponentially padded input `1 ^ (2 ^ (|x| ^ k) + k) 0 x` is defined as
`true`.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalPriceBit

open PEqualNP.Library PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

theorem bit_language : ∀ (r : List Bool → List Bool) (k : ℕ), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r → ∃ L : Language Bool, L ∈ PEqualNP.Library.EXP ∧ ∀ (x : List Bool) (s : ℕ) (T : List (Option Bool)), r (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → ∃ c : List Bool, c.length = 2 * x.length + 1 ∧ ∀ i : List Bool, (i ++ c ∈ L ↔ T.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 i) none = some true) := by
  intro r k hr
  refine ⟨{z : List Bool | bitTest r (padK k (bitU z), bitV z) = true}, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := PEqualNP.Library.L095 k bitU bitV (bitTest r) cpt_bitU cpt_bitV
      (cpt_bitTest hr)
    exact ⟨j, fun z => bitTest r (padK k (bitU z), bitV z), fun z => Iff.rfl, hj⟩
  · intro x s T e
    refine ⟨tailC x, length_tailC x, fun i => ?_⟩
    show bitTest r (padK k (bitU (i ++ tailC x)), bitV (i ++ tailC x)) = true ↔ _
    rw [bitU_app, bitV_app]
    exact bitTest_spec r _ i s T e

end PEqualNP.MetaComplexity.Helpers.LocalPriceBit
