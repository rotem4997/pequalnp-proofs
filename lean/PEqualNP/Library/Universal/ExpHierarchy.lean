import PEqualNP.Library.Universal.CompileBool
import PEqualNP.Library.Universal.VerifyCPT
import PEqualNP.Library.Universal.SStepCPT
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.Machines.FilterMap
import PEqualNP.Library.Machines.ExpPad
import PEqualNP.Library.Machines.ComposeTime
import PEqualNP.Library.Helpers.PolyExp
import PEqualNP.Library.Helpers.OutputLength

/-!
# A language decidable in exponential time outside P

Helper module (proofs only, no statement may use it). By diagonalization against the
polynomial-time interpreter `V` of `Verify.lean`: the language of all strings `z` whose leading
code, run on `z` itself with a clock of `2 ^ |z|` steps, does not answer `true`, is decided within
`2 ^ (n ^ k) + k` steps for some `k` (pad the input exponentially, then run a polynomial-time
test on the padded string) but is not in P.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines PEqualNP.Library.Machines.ExpPad

/-- The query put to the interpreter, read off a padded string. -/
def expQ (s : List Bool) : List Bool :=
  pairB (unpairB (dropN s)).1 (pairB (dropN s) (hd s))

/-- The acceptance test of the diagonal language, on a padded string. -/
def expG (s : List Bool) : Bool := !V (expQ s, [])

theorem hd_expPad (z : List Bool) : hd (expPad z) = un (2 ^ z.length) :=
  hd_un (2 ^ z.length) z

theorem dropN_expPad (z : List Bool) : dropN (expPad z) = z :=
  dropN_un (2 ^ z.length) z

theorem expQ_expPad (z : List Bool) :
    expQ (expPad z) = pairB (unpairB z).1 (pairB z (un (2 ^ z.length))) := by
  simp only [expQ, hd_expPad, dropN_expPad]

theorem expPad_length (z : List Bool) : (expPad z).length = 2 ^ z.length + z.length + 1 := by
  simp only [expPad, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The query is polynomial-time computable from the padded string. -/
theorem cpt_expQ :
    ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) expQ :=
  have h1 : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun s : List Bool => (unpairB (dropN s)).1) :=
    cpt_comp (g := fun s : List Bool => (unpairB s).1) cpt_dropN cpt_unpairB1
  cpt_pairB2 h1 (cpt_pairB2 cpt_dropN cpt_hd)

/-- The acceptance test is polynomial-time computable from the padded string. -/
theorem cpt_expG :
    ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool expG := by
  have h1 : ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun s : List Bool => V (expQ s, [])) :=
    cpt_comp (cpt_pair cpt_expQ (cpt_const [])) (cpt_V cpt_sstep)
  have h2 : ComputableInPolyTime Computability.encodeBool Computability.encodeBool
      (fun b : Bool => !b) :=
    filterMap_polyTime Computability.encodeBool Computability.encodeBool (fun b => !b)
      (fun b => some (!b)) (fun b => by cases b <;> rfl)
  exact cpt_comp (g := fun b : Bool => !b) h1 h2

/-- A function bounded by `2 ^ (c * (n + 1))` is bounded by `2 ^ (n ^ k) + k` for some `k`. -/
theorem exp_linear_le (b : ℕ → ℕ) (c : ℕ) (hb : ∀ n, b n ≤ 2 ^ (c * (n + 1))) :
    ∃ k, ∀ n, b n ≤ 2 ^ (n ^ k) + k := by
  refine ⟨c + 2 + b 0 + b 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact le_trans (by omega : b 0 ≤ c + 2 + b 0 + b 1) (Nat.le_add_left _ _)
    · exact le_trans (by omega : b 1 ≤ c + 2 + b 0 + b 1) (Nat.le_add_left _ _)
  · have h1 : c ≤ n ^ c := by
      have h2 : c < 2 ^ c := Nat.lt_two_pow_self
      have h3 : 2 ^ c ≤ n ^ c := Nat.pow_le_pow_left h c
      omega
    have h4 : n + 1 ≤ n ^ 2 := by nlinarith
    have h5 : c * (n + 1) ≤ n ^ (c + 2) := by
      rw [pow_add]
      exact Nat.mul_le_mul h1 h4
    have h6 : n ^ (c + 2) ≤ n ^ (c + 2 + b 0 + b 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h7 : (2 : ℕ) ^ (c * (n + 1)) ≤ 2 ^ (n ^ (c + 2 + b 0 + b 1)) :=
      Nat.pow_le_pow_right (by norm_num) (h5.trans h6)
    have := hb n
    omega

/-- The arithmetic bound: the time of padding followed by a polynomial-time test is at most
`2 ^ (n ^ k) + k` for some `k`. -/
theorem expTime_bound (p : Polynomial ℕ) :
    ∃ k, ∀ n : ℕ, 8 * 2 ^ n + 8 * n + 8 + (2 * (2 ^ n + n + 1) + 2) + p.eval (2 ^ n + n + 1) ≤
      2 ^ (n ^ k) + k := by
  obtain ⟨j, hj⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add p
  refine exp_linear_le _ (j + 6) (fun n => ?_)
  have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hm : 2 ^ n + n + 1 ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
  have h1 : (2 ^ n + n + 1) ^ j ≤ 2 ^ ((n + 1) * j) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hm j
  have h2 : j ≤ 2 ^ ((n + 1) * j) := by
    have h3 : j < 2 ^ j := Nat.lt_two_pow_self
    have h4 : (2 : ℕ) ^ j ≤ 2 ^ ((n + 1) * j) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  have h5 : (2 : ℕ) ^ ((n + 1) * j) * 2 ≤ 2 ^ ((n + 1) * (j + 5)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h6 : (2 : ℕ) ^ n * 32 ≤ 2 ^ ((n + 1) * (j + 5)) := by
    have : (2 : ℕ) ^ n * 32 = 2 ^ (n + 5) := by rw [pow_add]; norm_num
    rw [this]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h7 : (2 : ℕ) ^ ((n + 1) * (j + 5)) * 2 ≤ 2 ^ ((j + 6) * (n + 1)) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h8 := hj (2 ^ n + n + 1)
  omega

/-- The diagonal test composed with padding runs within `2 ^ (n ^ k) + k` for some `k`. -/
theorem expG_time : ∃ k : ℕ, ComputableInTime (fun x : List Bool => x) Computability.encodeBool
    (fun z : List Bool => expG (expPad z)) (fun n : ℕ => 2 ^ (n ^ k) + k) := by
  obtain ⟨p, hp⟩ := time_of_polyTime cpt_expG
  obtain ⟨k, hk⟩ := expTime_bound p
  have h := comp_time (fun x : List Bool => x) (fun x : List Bool => x) Computability.encodeBool
    expPad expG (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) (fun n => p.eval n)
    (fun n => 2 ^ n + n + 1) expPad_time hp (fun _ _ hxy => eval_mono p hxy)
    (fun a => (expPad_length a).le)
  exact ⟨k, time_mono h hk⟩

/-- The clock `2 ^ m` dominates the simulated polynomial running time at some length `m` above
any threshold. -/
theorem exp_clock (d : ℕ) (T : Polynomial ℕ) (N : ℕ) :
    ∃ m, N + 1 ≤ m ∧ d * T.eval m + d ≤ 2 ^ m := by
  obtain ⟨j, hj⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add T
  obtain ⟨m, hm, hlt⟩ := PEqualNP.Library.Helpers.exists_pow_lt (d * (j + 2)) j (N + 1)
  refine ⟨m, hm, ?_⟩
  have hP : 1 ≤ m ^ j := Nat.one_le_pow _ _ (by omega)
  have h1 : d * T.eval m ≤ d * (m ^ j + j) := Nat.mul_le_mul_left d (hj m)
  have h2 : d * (j + 1) * 1 ≤ d * (j + 1) * m ^ j := Nat.mul_le_mul_left _ hP
  have e : d * (j + 2) * m ^ j = d * m ^ j + d * (j + 1) * m ^ j := by ring
  have e2 : d * (m ^ j + j) + d = d * m ^ j + d * (j + 1) * 1 := by ring
  omega

theorem expHierarchy : ∃ L : Language Bool,
    (∃ k : ℕ, L ∈ PEqualNP.Library.DTIME (fun n : ℕ => 2 ^ (n ^ k) + k)) ∧
      L ∉ PEqualNP.Library.P := by
  let A : Language Bool := {z | expG (expPad z) = true}
  have hA : ∀ z, z ∈ A ↔ expG (expPad z) = true := fun _ => Iff.rfl
  refine ⟨A, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := expG_time
    exact ⟨k, fun z => expG (expPad z), fun _ => Iff.rfl, hk⟩
  rintro ⟨f, hf, ⟨cM⟩⟩
  have hf' : ∀ z, z ∈ A ↔ f z = true := hf
  obtain ⟨c, d, hc⟩ := compileBool cM.tm cM.inputAlphabet cM.outputAlphabet
  have hrun : ∀ z : List Bool, ∃ n, n ≤ cM.time.eval z.length ∧
      c.outputsWithin (z.map (fun b => cond b 1 0)) (d * n + d) [bitCode (f z)] := by
    intro z
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cM.time.eval z.length ∧
        (flip bind (Turing.TM2.step cM.tm.m))^[n]
          (some (Turing.initList cM.tm (z.map cM.inputAlphabet.invFun))) =
        some (Turing.haltList cM.tm [cM.outputAlphabet.invFun (f z)]) :=
      ⟨(cM.outputsFun z).steps, (cM.outputsFun z).steps_le_m, (cM.outputsFun z).evals_in_steps⟩
    exact ⟨n, hn, hc z (f z) n hev⟩
  obtain ⟨m, hm, hclock⟩ := exp_clock d cM.time (2 * (encCode c).length)
  let z : List Bool := pairB (encCode c) (un (m - (2 * (encCode c).length + 1)))
  have hzl : z.length = m := by
    simp only [z, pairB_length, un, List.length_replicate]
    omega
  have hq : expQ (expPad z) = pairB (encCode c) (pairB z (un (2 ^ m))) := by
    rw [expQ_expPad, hzl]
    simp only [z, unpairB_pairB]
  obtain ⟨n, hn, ho⟩ := hrun z
  have hle : d * n + d ≤ 2 ^ m := by
    rw [hzl] at hn
    have h2 : d * n ≤ d * cM.time.eval m := Nat.mul_le_mul_left d hn
    omega
  have ho' := Code.outputsWithin_mono c _ hle _ ho
  have hV : V (expQ (expPad z), []) = true ↔
      c.outputsWithin (z.map (fun b => cond b 1 0)) (2 ^ m) [1] := by
    rw [hq, V_spec]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.zero_le, true_and]
  have hiff : V (expQ (expPad z), []) = true ↔ f z = true := by
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
  have hneg : z ∈ A ↔ V (expQ (expPad z), []) = false := by
    rw [hA]
    simp only [expG, Bool.not_eq_true']
  have hcontra : V (expQ (expPad z), []) = true ↔ V (expQ (expPad z), []) = false :=
    hiff.trans ((hf' z).symm.trans hneg)
  cases hv : V (expQ (expPad z), []) with
  | true => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.1 rfl)
  | false => rw [hv] at hcontra; exact Bool.noConfusion (hcontra.2 rfl)

end PEqualNP.Library.Universal
