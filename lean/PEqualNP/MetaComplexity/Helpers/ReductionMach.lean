import PEqualNP.MetaComplexity.Helpers.ReductionPieces
import PEqualNP.MetaComplexity.L504
import PEqualNP.MetaComplexity.L506
import PEqualNP.Library.L007

/-!
# G-MACH: the map of record is computable in polynomial time

Part 3 of the assembly of L-meta-444. L-lib-007 compositions of the checked 506 (E
in unary), 507 (polynomials on unary tuples: [E, k] and [n]), 500 (renaming), 501 (the renamed
formula lies in the input subtype of 499), 499 (owner lists), the checked 504 (pairing) and 508
(printer), with bridge B5 (`retype`) at each change of description.
-/

namespace PEqualNP.MetaComplexity.Reduction

open PEqualNP.Search PEqualNP.CircuitLowerBounds PEqualNP.Library
open PEqualNP.MetaComplexity.Helpers.OwnerLink (OWN REN)

/-- The polynomial list giving [E, k] from [E]. -/
noncomputable def polyEk : List (MvPolynomial (Fin 1) ℕ) := [MvPolynomial.X 0, MvPolynomial.C kRec]

/-- The polynomial list giving [n] from [E]. -/
noncomputable def polyN : List (MvPolynomial (Fin 1) ℕ) :=
  [3 * (MvPolynomial.X 0 + 1) + 18 * MvPolynomial.C kRec * (MvPolynomial.X 0 + 1) ^ 2]

theorem mach_of_pieces (h499 : Stmt499) (h500 : Stmt500) (h501 : Stmt501) (h507 : Stmt507)
    (h508 : Stmt508) : ComputableInPolyTime encodeCNF PEqualNP.MetaComplexity.encodeLgp R := by
  have cE := PEqualNP.MetaComplexity.L506
  -- [E, k]
  have cEk0 := L007 _ _ _ _ _ _ _ _ _ _ _ cE (h507 1 polyEk)
  have cEk : ComputableInPolyTime encodeCNF (encodeList (fun a : ℕ => List.replicate a true ++ [false]))
      (fun φ : CNF => [Eof φ, kRec]) :=
    retype _ _ _ _ _ _ _ _ cEk0 (fun φ => by simp [polyEk, Eof])
  -- [n]
  have cN0 := L007 _ _ _ _ _ _ _ _ _ _ _ cE (h507 1 polyN)
  have cN : ComputableInPolyTime encodeCNF (encodeList (fun a : ℕ => List.replicate a true ++ [false]))
      (fun φ : CNF => [nOf (Eof φ) kRec]) :=
    retype _ _ _ _ _ _ _ _ cN0 (fun φ => by simp [polyN, nOf, Eof])
  -- ([E, k], REN φ), then into the input subtype of 499 (B5 with 501)
  have cPair := PEqualNP.MetaComplexity.L504 _ _ _ _ _ _ _ REN cEk h500
  have cIn : ComputableInPolyTime encodeCNF
      (fun p : List ℕ × {φ : PEqualNP.Search.CNF // ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum} => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ PEqualNP.Search.encodeCNF p.2.1)
      (fun φ : CNF => (([Eof φ, kRec] : List ℕ), (⟨REN φ, (h501 φ).2⟩ :
        {φ : PEqualNP.Search.CNF // ∀ c ∈ φ, ∀ l ∈ c, l.1 < (φ.map (fun c : PEqualNP.Search.Clause => c.length + 1)).sum}))) :=
    retype _ _ _ _ _ _ _ _ cPair (fun φ => rfl)
  -- the owner lists
  have cOl0 := L007 _ _ _ _ _ _ _ _ _ _ _ cIn h499
  have cOl : ComputableInPolyTime encodeCNF
      (encodeList (encodeList (fun a : ℕ => List.replicate a true ++ [false])))
      (fun φ : CNF => OWN (Eof φ) kRec (REN φ)) :=
    retype _ _ _ _ _ _ _ _ cOl0 (fun φ => rfl)
  -- ([n], owner lists), then the printer 508
  have cP := PEqualNP.MetaComplexity.L504 _ _ _ _ _ _ _ _ cN cOl
  have cR0 := L007 _ _ _ _ _ _ _ _ _ _ _ cP h508
  exact retype _ _ _ _ _ _ _ _ cR0 (fun φ => rfl)

end PEqualNP.MetaComplexity.Reduction
