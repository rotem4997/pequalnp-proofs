import Mathlib.Order.CompletePartialOrder
import PEqualNP.Library.Universal.Lazy
import PEqualNP.Library.Universal.LazyCPT

/-- NP is strictly inside NEXP: lazy diagonalization along a chain of padded inputs, with the
polynomial-time interpreter as verifier and a brute-force search at the end of the chain. -/
theorem PEqualNP.Library.L053 : PEqualNP.Library.NP ⊂ PEqualNP.Library.NEXP :=
  PEqualNP.Library.Universal.NP_ssubset_NEXP_of PEqualNP.Library.Universal.cpt_RD
