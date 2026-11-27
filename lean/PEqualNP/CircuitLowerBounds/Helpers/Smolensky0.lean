import PEqualNP.Defs
import Mathlib

/-!
# The approximation statement of Razborov and Smolensky

Helper module (proofs only, no statement may use it). The one hypothesis the degree lower
bound takes from the approximation method, as a named proposition: a circuit of size `s` and
depth `d` over AND, OR, NOT and MOD `p` agrees, outside a `s / 2 ^ l` fraction of the inputs,
with a polynomial over the field with `p` elements of degree at most `((p - 1) * l) ^ d`.
-/

namespace PEqualNP.CircuitLowerBounds.Helpers

open PEqualNP.CircuitLowerBounds

/-- Low-degree approximation of constant-depth circuits with MOD `p` gates. -/
def ApproxStatement : Prop :=
  ∀ (p : ℕ), Nat.Prime p → ∀ (n s d l : ℕ) (C : Circuit),
    (∀ g ∈ C.gates,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp)) →
    C.size ≤ s → C.depth n ≤ d → 1 ≤ l →
    ∃ P : MvPolynomial (Fin n) (ZMod p),
      P.totalDegree ≤ ((p - 1) * l) ^ d ∧
      (Finset.univ.filter fun x : Fin n → Bool =>
          MvPolynomial.eval (fun i => if x i = true then (1 : ZMod p) else 0) P ≠
            (if C.eval (List.ofFn x) = true then (1 : ZMod p) else 0)).card * 2 ^ l
        ≤ s * 2 ^ n

end PEqualNP.CircuitLowerBounds.Helpers
