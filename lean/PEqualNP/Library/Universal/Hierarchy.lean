import PEqualNP.Library.Universal.CompileBool
import PEqualNP.Library.Universal.VerifyCPT
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.L008
import PEqualNP.Library.L055

/-!
# A language in P outside a fixed polynomial time bound

Helper module (proofs only, no statement may use it). By diagonalization against the
polynomial-time interpreter `V` of `Verify.lean`: the language of all strings `z` whose leading
code, run on `z` itself with a clock of `|z| ^ (k + 2)` steps, does not answer `true`, is in P
but is not decided within `n ^ k + k` steps.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

/-- The query the diagonal language puts to the interpreter. -/
private def diagQ (K : ℕ) (z : List Bool) : List Bool :=
  pairB (unpairB z).1 (pairB z (un (z.length ^ K)))

/-- The diagonal query is polynomial-time computable. -/
private theorem cpt_diagQ (K : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) (diagQ K) := by
  have hclock : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => un (x.length ^ K)) := by
    have h := L055 (Polynomial.X ^ K)
    simp only [Polynomial.eval_pow, Polynomial.eval_X] at h
    exact h
  exact cpt_pairB2 cpt_unpairB1 (cpt_pairB2 cpt_id hclock)

/-- The acceptance test of the diagonal language is polynomial-time computable. -/
private theorem cpt_diagV (K : ℕ) :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun z : List Bool => V (diagQ K z, [])) :=
  cpt_comp (cpt_pair (cpt_diagQ K) (cpt_const [])) (cpt_V cpt_sstep)

/-- The clock of the diagonal language dominates the simulated running time. -/
private theorem clock_bound (d k m : ℕ) (hm : d + k + 2 ≤ m) :
    d * (m ^ k + k) + d ≤ m ^ (k + 2) := by
  have hP : 1 ≤ m ^ k := Nat.one_le_pow _ _ (by omega)
  have h1 : m ^ k * (k + 2) ≤ m ^ k * m := Nat.mul_le_mul_left _ (by omega)
  have h2 : 1 * (k + 1) ≤ m ^ k * (k + 1) := Nat.mul_le_mul_right _ hP
  have h3 : m ^ k + k + 1 ≤ m ^ k * m := by
    have e : m ^ k * (k + 2) = m ^ k * (k + 1) + m ^ k := by ring
    omega
  have h4 : d * (m ^ k + k + 1) ≤ m * (m ^ k * m) :=
    Nat.mul_le_mul (by omega) h3
  have e1 : d * (m ^ k + k) + d = d * (m ^ k + k + 1) := by ring
  have e2 : m ^ (k + 2) = m * (m ^ k * m) := by ring
  rw [e1, e2]
  exact h4

theorem hierarchy (k : ℕ) :
    ∃ L ∈ PEqualNP.Library.P, L ∉ PEqualNP.Library.DTIME (fun n : ℕ => n ^ k + k) := by
  let A : Language Bool := {z | V (diagQ (k + 2) z, []) = true}
  have hA : ∀ z, z ∈ A ↔ V (diagQ (k + 2) z, []) = true := fun _ => Iff.rfl
  have hAP : A ∈ PEqualNP.Library.P :=
    ⟨fun z => V (diagQ (k + 2) z, []), fun _ => Iff.rfl, cpt_diagV (k + 2)⟩
  refine ⟨Aᶜ, L008 A hAP, ?_⟩
  rintro ⟨f, hf, cM, htime⟩
  have hf' : ∀ z, z ∉ A ↔ f z = true := hf
  obtain ⟨c, d, hc⟩ := compileBool cM.tm cM.inputAlphabet cM.outputAlphabet
  have hrun : ∀ z : List Bool, ∃ n, n ≤ cM.time z.length ∧
      c.outputsWithin (z.map (fun b => cond b 1 0)) (d * n + d) [bitCode (f z)] := by
    intro z
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cM.time z.length ∧
        (flip bind (Turing.TM2.step cM.tm.m))^[n]
          (some (Turing.initList cM.tm (z.map cM.inputAlphabet.invFun))) =
        some (Turing.haltList cM.tm [cM.outputAlphabet.invFun (f z)]) :=
      ⟨(cM.outputsFun z).steps, (cM.outputsFun z).steps_le_m, (cM.outputsFun z).evals_in_steps⟩
    exact ⟨n, hn, hc z (f z) n hev⟩
  let z : List Bool := pairB (encCode c) (un (d + k + 2))
  have hzl : d + k + 2 ≤ z.length := by
    simp only [z, pairB_length, un, List.length_replicate]
    omega
  have hq : diagQ (k + 2) z = pairB (encCode c) (pairB z (un (z.length ^ (k + 2)))) := by
    simp only [diagQ, z, unpairB_pairB]
  obtain ⟨n, hn, ho⟩ := hrun z
  have hle : d * n + d ≤ z.length ^ (k + 2) := by
    have h1 : n ≤ z.length ^ k + k := hn.trans (htime z.length)
    have h2 : d * n ≤ d * (z.length ^ k + k) := Nat.mul_le_mul_left d h1
    have h3 := clock_bound d k z.length hzl
    omega
  have ho' := Code.outputsWithin_mono c _ hle _ ho
  have hV : V (diagQ (k + 2) z, []) = true ↔
      c.outputsWithin (z.map (fun b => cond b 1 0)) (z.length ^ (k + 2)) [1] := by
    rw [hq, V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
  have hiff : z ∈ A ↔ f z = true := by
    rw [hA, hV]
    constructor
    · intro h1
      have heq : [1] = [bitCode (f z)] := h1.2.symm.trans ho'.2
      cases hb : f z with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    · intro hb
      rw [hb] at ho'
      exact ho'
  have hcontra : z ∈ A ↔ z ∉ A := hiff.trans (hf' z).symm
  by_cases hz : z ∈ A
  · exact (hcontra.1 hz) hz
  · exact hz (hcontra.2 hz)

end PEqualNP.Library.Universal
