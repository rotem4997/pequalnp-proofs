import PEqualNP.Defs.Oracle
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Extension oracles, for the algebrization barrier

Needed to state the algebrization barrier (Aaronson and Wigderson, ACM Trans. Comput. Theory
1(1), 2009) on this project's oracle machines (`Defs/Oracle.lean`).

* Every finite field is isomorphic to `GaloisField p k` for a prime `p`, so an extension of an
  oracle is given over these fields: `AlgExtension` assigns a polynomial in `m` variables over
  `GaloisField p k` to every prime `p`, every `k` and every arity `m`.
* `IsMultiquadraticExtension A E`: every polynomial of `E` has degree at most 2 in each
  variable, and on the Boolean cube it equals the oracle `A` (a point `x` of `{0,1}^m` is the
  string `List.ofFn x`). Aaronson and Wigderson allow any constant bound on the degree in each
  variable; their separations use 2, and a separation stated with an existential extension of
  degree 2 is one of theirs.
* A machine names a field element by a natural number. `FieldCodes` is a choice of such names,
  one injective map per field. The theorem is stated for EVERY injective choice, so it covers
  any representation in which a machine can compute field operations itself.
* `extOracle codes E` is a language: a query names `p`, `k`, `m`, a point `y` of
  `GaloisField p k ^ m` and a bit position `j`; the answer is bit `j` of the name of the value
  of `E p k m` at `y`. One query reveals one bit of one value; a machine reads a whole value
  with polynomially many queries. Every number is written self-delimiting, so a query string
  names at most one tuple.
-/

namespace PEqualNP.Library

/-- A natural number in binary, self-delimiting: each bit is preceded by `true`, and `false`
ends the number. -/
def algEncodeNat (m : ℕ) : List Bool :=
  (Nat.bits m).flatMap (fun b => [true, b]) ++ [false]

/-- A family of polynomials: for every prime `p`, every `k` and every arity `m`, a polynomial
in `m` variables over `GaloisField p k`. -/
def AlgExtension : Type :=
  ∀ (p : ℕ) [Fact p.Prime] (k m : ℕ), MvPolynomial (Fin m) (GaloisField p k)

open Classical in
/-- `E` extends the oracle `A` with degree at most 2 in each variable, over every finite
field. Membership in `A` is decided classically. -/
def IsMultiquadraticExtension (A : Language Bool) (E : AlgExtension) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k m : ℕ),
    (∀ i : Fin m, MvPolynomial.degreeOf i (E p k m) ≤ 2) ∧
    ∀ x : Fin m → Bool,
      MvPolynomial.eval (fun i => if x i then (1 : GaloisField p k) else 0) (E p k m) =
        if List.ofFn x ∈ A then 1 else 0

/-- Names of field elements: one map to the naturals for every field `GaloisField p k`. -/
def FieldCodes : Type :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), GaloisField p k → ℕ

/-- Every field's naming map is injective. -/
def FieldCodes.Injective (codes : FieldCodes) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Function.Injective (codes p k)

/-- The oracle that answers bit `j` of the name of `E p k m` at the point `y`. -/
def extOracle (codes : FieldCodes) (E : AlgExtension) : Language Bool :=
  {s | ∃ (p : ℕ) (_ : Fact p.Prime) (k m : ℕ) (y : Fin m → GaloisField p k) (j : ℕ),
      s = algEncodeNat p ++ algEncodeNat k ++ algEncodeNat m ++
          (List.ofFn fun i => algEncodeNat (codes p k (y i))).flatten ++ algEncodeNat j ∧
      (codes p k (MvPolynomial.eval y (E p k m))).testBit j = true}

end PEqualNP.Library
