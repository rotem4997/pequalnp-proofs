import PEqualNP.MetaComplexity.Helpers.Verifier
import PEqualNP.MetaComplexity.Helpers.Machines.Glue

/-!
# The partial MCSP verifier runs in polynomial time

Assembly for `L-meta-021`: each conjunct of `verify` is a transducer output, an equality or a
length comparison of transducer outputs, or the output transducer after the iterated step, so
the glue lemmas make the whole verifier a polynomial-time decision on the pair.
-/

namespace PEqualNP.MetaComplexity.Helpers.Machines

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.MetaComplexity.Helpers

theorem verify_polyTime :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => verify p.1 (dec4 p.2)) := by
  have h1 := pair_allTrue (cpt_fstRun2_comp sym_dec4_snd δwf finWf (WfQ.start true true))
  have h2 := sym_eq_append_run δsucc finSucc SuccQ.carry δtail finTail false δhead finHead false
  have h3 := pair_eq (cpt_fstRun2_comp sym_dec4_snd δtab finTab ())
    (cpt_fstRun2_comp cpt_fst δinst finInst false)
  have h4 := pair_lenLE (cpt_fstRun2_comp cpt_fst δunary finUnary false)
    (cpt_fstRun2_comp sym_dec4_snd δgates finGates (GQ.run false))
  have h5 := pair_allTrue (cpt_fstRun2_comp
    (sym_iter δstep finStep StepQ.start step_length_le sym_dec4_snd cpt_fst) δout finOut OutQ.init)
  have h6 := pair_allTrue (cpt_fstRun2_comp cpt_fst δsep finSep false)
  exact cpt_congr (pair_and (pair_and (pair_and (pair_and (pair_and h1 h2) h3) h4) h5) h6)
    (fun p => rfl)

theorem partialMCSP_mem_NP : PEqualNP.MetaComplexity.PartialMCSP ∈ NP := by
  obtain ⟨q, hq⟩ := verify_iff
  exact np_of_sym_verifier _ verify q verify_polyTime hq

end PEqualNP.MetaComplexity.Helpers.Machines
