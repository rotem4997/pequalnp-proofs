import PEqualNP.MetaComplexity.Helpers.LocalPrice
import PEqualNP.MetaComplexity.Helpers.LocalPriceBit

/-!
# The price of a uniform local reduction of parity, in one statement

`LocalPrice.price_uniform` applied to `LocalPriceBit.bit_language`.
-/

namespace PEqualNP.MetaComplexity.Helpers.LocalPriceU

theorem uniform : ∀ (r : List Bool → List Bool) (k : ℕ), PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) r → ∃ L : Language Bool, L ∈ PEqualNP.Library.EXP ∧ ∀ S : ℕ → ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE S → ∀ (x : List Bool) (n q M : ℕ) (w : (Fin n → Bool) → List Bool), 0 < q → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ y : Fin n → Bool, (w y).length ≤ M) → (∀ y : Fin n → Bool, (Finset.univ.filter fun i : Fin n => y i = true).card % 2 = 1 ↔ w y ∈ PEqualNP.MetaComplexity.PartialMCSP) → 3 * q < n → w (fun _ : Fin n => false) = r (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) → ∀ (n' s : ℕ) (T : List (Option Bool)), r (List.replicate (2 ^ (x.length ^ k) + k) true ++ false :: x) = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial T → T.length = 2 ^ n' → s ≤ S (n' + (2 * x.length + 1)) ∧ (n - 3 * q) / (4 * q) < (2 * S (n' + (2 * x.length + 1)) + 3) * (Nat.log 2 M + 3) + Nat.log 2 q :=
  PEqualNP.MetaComplexity.Helpers.LocalPrice.price_uniform
    PEqualNP.MetaComplexity.Helpers.LocalPriceBit.bit_language

end PEqualNP.MetaComplexity.Helpers.LocalPriceU
