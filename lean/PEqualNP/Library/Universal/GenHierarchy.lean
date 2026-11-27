import PEqualNP.Library.Universal.CompileBool
import PEqualNP.Library.Universal.VerifyCPT
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.FilterMap
import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.Machines.FirstTime
import PEqualNP.Library.Helpers.PolyExp

/-!
# The time hierarchy for time-constructible bounds, with a fixed polynomial gap

Helper module (proofs only, no statement may use it). By diagonalization against the
polynomial-time interpreter `V` of `Verify.lean`: for a bound `t` with `n ≤ t n` whose clock
`x ↦ 1 ^ t |x|` is computed within `c * t n + c` steps, the language of all strings `z` whose
leading code, run on `z` itself with a clock of `t |z| * |z|` steps, does not answer `true`, is
decided within `c' * t n ^ k + c'` steps for a fixed `k` (compute the clock, then run a fixed
polynomial-time test on the pair of the clock and the input) but not within `t n` steps.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

/-- The query put to the interpreter, read off the string `pairB u x` where `u` is the clock. -/
def genQ (s : List Bool) : List Bool :=
  pairB (unpairB (unpairB s).2).1 (pairB (unpairB s).2 (mulU (unpairB s).1 (unpairB s).2))

/-- The acceptance test of the diagonal language, on the string `pairB u x`. -/
def genG (s : List Bool) : Bool := !V (genQ s, [])

theorem genQ_pairB (u x : List Bool) :
    genQ (pairB u x) = pairB (unpairB x).1 (pairB x (un (u.length * x.length))) := by
  simp only [genQ, unpairB_pairB, mulU]

/-- The query is polynomial-time computable. -/
theorem cpt_genQ :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) genQ :=
  have h2 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB s).2) := cpt_unpairB2
  have h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB (unpairB s).2).1) :=
    cpt_comp (g := fun s : List Bool => (unpairB s).1) h2 cpt_unpairB1
  cpt_pairB2 h1 (cpt_pairB2 h2 (cpt_mulU2 cpt_unpairB1 h2))

/-- The acceptance test is polynomial-time computable, on pairs. -/
theorem cpt_genG :
    ComputableInPolyTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => genG (pairB p.1 p.2)) := by
  have h1 : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V (genQ s, [])) :=
    cpt_comp (cpt_pair cpt_genQ (cpt_const [])) (cpt_V cpt_sstep)
  have h2 : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime Computability.encodeBool Computability.encodeBool (fun b => !b)
      (fun b => some (!b)) (fun b => by cases b <;> rfl)
  have h3 : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool genG :=
    cpt_comp (g := fun b : Bool => !b) h1 h2
  exact cpt_comp (g := genG) cpt_pairB h3

/-- The arithmetic bound: the time of the clock followed by the test is polynomial in `t n`. -/
theorem gen_arith (j1 j2 c T n : ℕ) (hn : n ≤ T) :
    c * T + c + 2 * T + (n ^ j1 + j1) + (2 * (T + n) + 2) + ((T + n) ^ j2 + j2) ≤
      (c + 8 + 2 ^ j2 + j1 + j2) * T ^ (j1 + j2 + 1) + (c + 8 + 2 ^ j2 + j1 + j2) := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have hn0 : n = 0 := by omega
    subst hn0
    have h1 : (0 : ℕ) ^ j1 ≤ 1 := by rcases j1 with _ | j <;> simp
    have h2 : (0 + 0 : ℕ) ^ j2 ≤ 1 := by rcases j2 with _ | j <;> simp
    have h3 : 1 ≤ 2 ^ j2 := Nat.one_le_two_pow
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at h2 ⊢
    have h4 := Nat.zero_le ((c + 8 + 2 ^ j2 + j1 + j2) * 0 ^ (j1 + j2 + 1))
    omega
  · have hP1 : T ≤ T ^ (j1 + j2 + 1) := Nat.le_self_pow (by omega) T
    have hP2 : n ^ j1 ≤ T ^ (j1 + j2 + 1) :=
      (Nat.pow_le_pow_left hn j1).trans (Nat.pow_le_pow_right hT (by omega))
    have hP3 : (T + n) ^ j2 ≤ 2 ^ j2 * T ^ (j1 + j2 + 1) := by
      have : (T + n) ^ j2 ≤ (2 * T) ^ j2 := Nat.pow_le_pow_left (by omega) j2
      rw [Nat.mul_pow] at this
      exact this.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT (by omega)))
    have hP4 : c * T ≤ c * T ^ (j1 + j2 + 1) := Nat.mul_le_mul_left c hP1
    have e : (c + 8 + 2 ^ j2 + j1 + j2) * T ^ (j1 + j2 + 1) =
        c * T ^ (j1 + j2 + 1) + 8 * T ^ (j1 + j2 + 1) + 2 ^ j2 * T ^ (j1 + j2 + 1) +
          j1 * T ^ (j1 + j2 + 1) + j2 * T ^ (j1 + j2 + 1) := by ring
    rw [e]
    generalize T ^ (j1 + j2 + 1) = P at *
    generalize 2 ^ j2 = B at *
    generalize B * P = BP at *
    generalize c * P = cP at *
    generalize c * T = cT at *
    generalize j1 * P = jP at *
    generalize j2 * P = jP' at *
    generalize (T + n) ^ j2 = X at *
    generalize n ^ j1 = Y at *
    omega

/-- The clock `t m * m` dominates the simulated running time. -/
theorem gen_clock (d n T m : ℕ) (hn : n ≤ T) (hm : 2 * d + 1 ≤ m) (hT : m ≤ T) :
    d * n + d ≤ T * m := by
  have h1 : d * n ≤ d * T := Nat.mul_le_mul_left d hn
  have h2 : d * 1 ≤ d * T := Nat.mul_le_mul_left d (by omega)
  have h3 : T * (2 * d) ≤ T * m := Nat.mul_le_mul_left T (by omega)
  have e : T * (2 * d) = d * T + d * T := by ring
  omega

theorem genHierarchy : ∃ k : ℕ, ∀ t : ℕ → ℕ, (∀ n : ℕ, n ≤ t n) →
    (∃ c : ℕ, PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
      (fun x : List Bool => x) (fun x : List Bool => List.replicate (t x.length) true)
      (fun n : ℕ => c * t n + c)) →
    ∃ L : Language Bool,
      (∃ c : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => c * t n ^ k + c)) ∧
        L ∉ PEqualNP.Library.DTIME t := by
  obtain ⟨p, hp⟩ := clockPair_time
  obtain ⟨j1, hj1⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add p
  obtain ⟨q, hq⟩ := time_of_polyTime cpt_genG
  obtain ⟨j2, hj2⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add q
  have hG : ComputableInTime encodePair Computability.encodeBool
      (fun p : List Bool × List Bool => genG (pairB p.1 p.2)) (fun m => m ^ j2 + j2) :=
    time_mono hq hj2
  refine ⟨j1 + j2 + 1, fun t ht hclock => ?_⟩
  let A : Language Bool := {z | genG (pairB (List.replicate (t z.length) true) z) = true}
  have hA : ∀ z, z ∈ A ↔ genG (pairB (un (t z.length)) z) = true := fun _ => Iff.rfl
  refine ⟨A, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hclock
    have h := comp_time (fun x : List Bool => x) encodePair Computability.encodeBool
      (fun x : List Bool => (List.replicate (t x.length) true, x))
      (fun p : List Bool × List Bool => genG (pairB p.1 p.2))
      (fun n => c * t n + c + 2 * t n + p.eval n) (fun m => m ^ j2 + j2)
      (fun n => t n + n) (hp t c hc) hG
      (fun _ _ hxy => Nat.add_le_add_right (Nat.pow_le_pow_left hxy j2) j2)
      (fun a => by simp [encodePair])
    refine ⟨c + 8 + 2 ^ j2 + j1 + j2,
      fun z => genG (pairB (List.replicate (t z.length) true) z), fun _ => Iff.rfl,
      time_mono h (fun n => ?_)⟩
    have h1 := gen_arith j1 j2 c (t n) n (ht n)
    have h2 := hj1 n
    show c * t n + c + 2 * t n + p.eval n + (2 * (t n + n) + 2) + ((t n + n) ^ j2 + j2) ≤ _
    omega
  rintro ⟨f, hf, cM, htime⟩
  have hf' : ∀ z, z ∈ A ↔ f z = true := hf
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
  let z : List Bool := pairB (encCode c) (un (2 * d + 1))
  have hzl : 2 * d + 1 ≤ z.length := by
    simp only [z, pairB_length, un, List.length_replicate]
    omega
  have hq : genQ (pairB (un (t z.length)) z) =
      pairB (encCode c) (pairB z (un (t z.length * z.length))) := by
    rw [genQ_pairB, un_length]
    simp only [z, unpairB_pairB]
  obtain ⟨n, hn, ho⟩ := hrun z
  have hle : d * n + d ≤ t z.length * z.length :=
    gen_clock d n (t z.length) z.length (hn.trans (htime z.length)) hzl (ht z.length)
  have ho' := Code.outputsWithin_mono c _ hle _ ho
  have hV : V (genQ (pairB (un (t z.length)) z), []) = true ↔
      c.outputsWithin (z.map (fun b => cond b 1 0)) (t z.length * z.length) [1] := by
    rw [hq, V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
  have hiff : V (genQ (pairB (un (t z.length)) z), []) = true ↔ f z = true := by
    rw [hV]
    constructor
    · intro h1
      have heq : [1] = [bitCode (f z)] := h1.2.symm.trans ho'.2
      cases hb : f z with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    · intro hb
      rw [hb] at ho'
      exact ho'
  have hneg : z ∈ A ↔ V (genQ (pairB (un (t z.length)) z), []) = false := by
    rw [hA]
    simp only [genG, Bool.not_eq_true']
  have hcontra : V (genQ (pairB (un (t z.length)) z), []) = true ↔
      V (genQ (pairB (un (t z.length)) z), []) = false :=
    hiff.trans ((hf' z).symm.trans hneg)
  cases hv : V (genQ (pairB (un (t z.length)) z), []) with
  | true => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.1 rfl)
  | false => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.2 rfl)

end PEqualNP.Library.Universal
