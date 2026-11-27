import PEqualNP.Library.Universal.Assembly
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Universal.VerifyCPT

/-- Some language is NP-complete: the strings (code, input, unary budget) for which some witness
no longer than the string makes the coded micro-instruction program accept within the budget.
The verifier is a polynomial-time interpreter; every NP verifier compiles to a code. -/
theorem PEqualNP.Library.L015 : ∃ L : Language Bool, PEqualNP.Library.NPComplete L :=
  PEqualNP.Library.Universal.npComplete_of_interp PEqualNP.Library.Universal.encCode
    PEqualNP.Library.Universal.V
    (PEqualNP.Library.Universal.cpt_V PEqualNP.Library.Universal.cpt_sstep)
    PEqualNP.Library.Universal.V_spec
