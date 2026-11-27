import PEqualNP.Library.Universal.LazyDefs
import PEqualNP.Library.Universal.Compile
import PEqualNP.Library.Machines.Pairing
import PEqualNP.Library.L045
import PEqualNP.Library.L048
import PEqualNP.Library.Helpers.PolyExp

/-!
# The lazy diagonal language is not in NP

Helper module (proofs only, no statement may use it). The language `DLang` of `LazyDefs.lean`
is outside NP, by lazy diagonalization along the chain `y₀ ++ un m`; and if the relation `RD` is
polynomial-time computable then NP is strictly contained in NEXP.
-/

namespace PEqualNP.Library.Universal

open PEqualNP.Library PEqualNP.Library.Machines

/-! ### The interpreter on NP languages -/

private theorem map_symIn_encodePair' (x w : List Bool) :
    (encodePair (x, w)).map symIn =
      x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2) := by
  simp only [encodePair, List.map_append, List.map_map]
  congr 1 <;> (apply List.map_congr_left; intro b _; cases b <;> rfl)

/-- Every language in NP is recognized by a code under the interpreter `V`, with any budget
above a polynomial in the input length; and acceptance within any budget is sound. -/
theorem np_code (L : Language Bool) (hL : L ∈ NP) :
    ∃ (c : Code) (q : Polynomial ℕ),
      (∀ (y : List Bool) (t : ℕ), q.eval y.length ≤ t → y ∈ L →
        ∃ w : List Bool, V (pairB (encCode c) (pairB y (un t)), w) = true) ∧
      (∀ (y : List Bool) (t : ℕ) (w : List Bool),
        V (pairB (encCode c) (pairB y (un t)), w) = true → y ∈ L) := by
  obtain ⟨R, p, ⟨fR, hfR, ⟨cR⟩⟩, hbound, hL⟩ := L045 L hL
  obtain ⟨c, d, hc⟩ := compile cR.tm cR.inputAlphabet cR.outputAlphabet
  have hrun : ∀ x w : List Bool, ∃ n, n ≤ cR.time.eval (x.length + w.length) ∧
      c.outputsWithin (x.map (fun b => cond b 1 0) ++ w.map (fun b => cond b 3 2))
        (d * n + d) [bitCode (fR (x, w))] := by
    intro x w
    obtain ⟨n, hn, hev⟩ : ∃ n, n ≤ cR.time.eval (encodePair (x, w)).length ∧
        (flip bind (Turing.TM2.step cR.tm.m))^[n]
          (some (Turing.initList cR.tm ((encodePair (x, w)).map cR.inputAlphabet.invFun))) =
        some (Turing.haltList cR.tm [cR.outputAlphabet.invFun (fR (x, w))]) :=
      ⟨(cR.outputsFun (x, w)).steps, (cR.outputsFun (x, w)).steps_le_m,
        (cR.outputsFun (x, w)).evals_in_steps⟩
    have h := hc (encodePair (x, w)) (fR (x, w)) n hev
    rw [map_symIn_encodePair'] at h
    refine ⟨n, ?_, h⟩
    simpa [encodePair] using hn
  let q : Polynomial ℕ :=
    p + Polynomial.C d * cR.time.comp (Polynomial.X + p) + Polynomial.C d
  have hq : ∀ n : ℕ, q.eval n = p.eval n + d * cR.time.eval (n + p.eval n) + d := by
    intro n
    simp [q, Polynomial.eval_comp]
  refine ⟨c, q, ?_, ?_⟩
  · intro x t ht hx
    obtain ⟨w, hw⟩ := (hL x).1 hx
    have hwl : w.length ≤ p.eval x.length := hbound x w hw
    have hwt : w.length ≤ q.eval x.length := by rw [hq]; omega
    refine ⟨w, (V_spec c x w t).2 ⟨hwt.trans ht, ?_⟩⟩
    obtain ⟨n, hn, ho⟩ := hrun x w
    have hfw : fR (x, w) = true := (hfR (x, w)).1 hw
    rw [hfw] at ho
    have hle : d * n + d ≤ q.eval x.length := by
      rw [hq]
      have h1 : n ≤ cR.time.eval (x.length + p.eval x.length) :=
        hn.trans (eval_mono _ (by omega))
      have h2 : d * n ≤ d * cR.time.eval (x.length + p.eval x.length) :=
        Nat.mul_le_mul_left d h1
      omega
    exact Code.outputsWithin_mono c _ (hle.trans ht) _ ho
  · intro x t w hVw
    obtain ⟨-, ho⟩ := (V_spec c x w t).1 hVw
    obtain ⟨n, -, ho'⟩ := hrun x w
    have h1 := Code.outputsWithin_mono c _ (le_max_left t (d * n + d)) _ ho
    have h2 := Code.outputsWithin_mono c _ (le_max_right t (d * n + d)) _ ho'
    have heq : [1] = [bitCode (fR (x, w))] := h1.2.symm.trans h2.2
    have hfw : fR (x, w) = true := by
      cases hb : fR (x, w) with
      | true => rfl
      | false => rw [hb] at heq; simp [bitCode] at heq
    exact (hL x).2 ⟨w, (hfR (x, w)).2 hfw⟩

/-! ### Facts about `V` on arbitrary code strings -/

/-- `V` only looks at the length of the budget. -/
theorem V_budget (cs x b w : List Bool) :
    V (pairB cs (pairB x b), w) = V (pairB cs (pairB x (un b.length)), w) := by
  simp [V, unpairB_pairB]

/-- `V` rejects every witness longer than the budget. -/
theorem V_length (cs x b w : List Bool) (h : V (pairB cs (pairB x b), w) = true) :
    w.length ≤ b.length := by
  simp only [V, unpairB_pairB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-! ### The relation along a chain -/

/-- The chain of inputs with code string `cs` and padding `au`. -/
def zc (cs au : List Bool) (m : ℕ) : List Bool := pairB cs (pairB au (un m))

theorem zc_length (cs au : List Bool) (m : ℕ) :
    (zc cs au m).length = (zc cs au 0).length + m := by
  simp [zc, pairB_length]
  omega

theorem zc_succ (cs au : List Bool) (m : ℕ) : zc cs au m ++ [true] = zc cs au (m + 1) := by
  simp [zc, pairB, un, List.replicate_succ']

theorem csOf_zc (cs au : List Bool) (m : ℕ) : csOf (zc cs au m) = cs := by
  simp [csOf, zc, unpairB_pairB]

theorem muOf_zc (cs au : List Bool) (m : ℕ) : muOf (zc cs au m) = un m := by
  simp [muOf, zc, unpairB_pairB]

theorem y0Of_zc (cs au : List Bool) (m : ℕ) : y0Of (zc cs au m) = zc cs au 0 := by
  simp [y0Of, zc, unpairB_pairB]

theorem un_tail (m : ℕ) : (un m).tail = un (m - 1) := by
  cases m <;> simp [un, List.replicate_succ]

/-- Below the threshold, the relation asks the code about the next input of the chain. -/
theorem RD_below (cs au : List Bool) (m : ℕ) (w : List Bool)
    (hC : ¬ (zc cs au 0).length ≤ Nat.size (Nat.size m)) :
    RD (zc cs au m, w) =
      V (pairB cs (pairB (zc cs au (m + 1)) (unpairB w).2), (unpairB w).1) := by
  simp [RD, csOf_zc, muOf_zc, y0Of_zc, condC_un, hC, zc_succ]

/-- At the first position past the threshold, the relation says that the code has no accepted
witness on the start of the chain within the budget. -/
theorem RD_at (cs au : List Bool) (m : ℕ) (w : List Bool)
    (hC : (zc cs au 0).length ≤ Nat.size (Nat.size m))
    (hC' : ¬ (zc cs au 0).length ≤ Nat.size (Nat.size (m - 1))) :
    RD (zc cs au m, w) = true ↔
      ∀ w' : List Bool, V (pairB cs (pairB (zc cs au 0) (un (Nat.size m))), w') = false := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hC' hC
  simp only [RD, csOf_zc, muOf_zc, y0Of_zc, condC_un, un_tail, hC, hC', decide_true,
    decide_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.false_or,
    List.isEmpty_iff, srch_eq_nil, lgU_un, List.length_append, un_length]
  constructor
  · intro h w'
    by_contra hV
    rw [Bool.not_eq_false] at hV
    have hlen : w'.length ≤ Nat.size m := by simpa using V_length _ _ _ _ hV
    have h1 := idx_lt_of_length_le hlen
    have h2 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (by
      have : 0 < Nat.size m := Nat.size_pos.2 (by omega)
      omega)
    have h3 : 2 ^ (Nat.size m + 1) = 2 ^ (Nat.size m - 1) * 4 := by
      have : Nat.size m + 1 = (Nat.size m - 1) + 2 := by
        have : 0 < Nat.size m := Nat.size_pos.2 (by omega)
        omega
      rw [this, pow_add]; norm_num
    have h4 := h (idx w') (by omega)
    rw [cand_idx, hV] at h4
    exact Bool.noConfusion h4
  · intro h j _
    exact h _

/-! ### Arithmetic -/

private theorem arith1 (k n : ℕ) (h : k + 3 ≤ n) : 3 * ((n + 1) ^ k + k) + 1 ≤ 2 ^ (n ^ 2) := by
  have h1 : (n + 1) ^ k ≤ 2 ^ (n * k) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_two_pow_self k
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have hA : 0 < 2 ^ (n * k) := by positivity
  have hB : 0 < 2 ^ k := by positivity
  have h3 : 2 ^ (n * k + k + 3) = 8 * (2 ^ (n * k) * 2 ^ k) := by
    rw [pow_add, pow_add]; ring
  have h4 : 2 ^ (n * k + k + 3) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by omega) (by nlinarith)
  nlinarith [Nat.mul_le_mul hA hB]

private theorem arith2 (k s : ℕ) (h : 2 * k + 2 ≤ s) :
    (2 ^ (2 * s)) ^ k + k ≤ 2 ^ (2 ^ (2 * s) - 1) := by
  have h1 : (2 ^ (2 * s)) ^ k = 2 ^ (2 * s * k) := (pow_mul 2 (2 * s) k).symm
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : 2 ^ k ≤ 2 ^ (2 * s * k) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h4 : 2 ^ (2 * s * k + 1) = 2 * 2 ^ (2 * s * k) := by rw [pow_succ]; ring
  have h5 : s < 2 ^ s := Nat.lt_two_pow_self
  have h6 : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [two_mul, pow_add]
  have h7 : 2 * s * k + 1 ≤ 2 ^ (2 * s) - 1 := by
    have : 2 * s * k + 2 ≤ 2 ^ s * 2 ^ s := by nlinarith
    omega
  have h8 : 2 ^ (2 * s * k + 1) ≤ 2 ^ (2 ^ (2 * s) - 1) :=
    Nat.pow_le_pow_right (by omega) h7
  omega

/-! ### The diagonal argument -/

theorem DLang_not_NP : DLang ∉ PEqualNP.Library.NP := by
  intro hD
  obtain ⟨c, q, hfwd, hbwd⟩ := np_code DLang hD
  obtain ⟨k, hk⟩ := PEqualNP.Library.Helpers.polynomial_le_pow_add q
  -- the padding
  have hs5 : 2 * k + (encCode c).length + 3 < 2 ^ (2 * k + (encCode c).length + 3) :=
    Nat.lt_two_pow_self
  have hn6 : 2 ^ (2 * (2 * k + (encCode c).length + 3)) =
      2 ^ (2 * k + (encCode c).length + 3) * 2 ^ (2 * k + (encCode c).length + 3) := by
    rw [two_mul, pow_add]
  have hn2 : 2 ^ (2 * (2 * k + (encCode c).length + 3)) =
      2 * 2 ^ (2 * (2 * k + (encCode c).length + 3) - 1) := by
    rw [← pow_succ']; congr 1
  have hnbig : 2 * (2 * k + (encCode c).length + 3) ≤
      2 ^ (2 * (2 * k + (encCode c).length + 3)) := by nlinarith
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 * (encCode c).length + 2 * a + 2 =
      2 ^ (2 * (2 * k + (encCode c).length + 3)) :=
    ⟨2 ^ (2 * (2 * k + (encCode c).length + 3) - 1) - (encCode c).length - 1, by omega⟩
  have harith2 := arith2 k (2 * k + (encCode c).length + 3) (by omega)
  generalize 2 ^ (2 * (2 * k + (encCode c).length + 3)) = n at *
  generalize hcs : encCode c = cs at *
  have hl : (zc cs (un a) 0).length = n := by
    simp [zc, pairB_length]
    omega
  have hz : ∀ m, (zc cs (un a) m).length = n + m := fun m => by rw [zc_length, hl]
  -- (i) room for the witness
  have hroom : ∀ N : ℕ, n ≤ N → 3 * q.eval (N + 1) + 1 ≤ 2 ^ (N ^ 2) + 2 := by
    intro N hN
    have h1 := hk (N + 1)
    have h2 := arith1 k N (by omega)
    omega
  -- the threshold
  have hex : ∃ m : ℕ, n ≤ Nat.size (Nat.size m) := by
    refine ⟨2 ^ 2 ^ n, ?_⟩
    rw [Nat.size_pow]
    have h1 : n < Nat.size (2 ^ n + 1) := Nat.lt_size.2 (by omega)
    exact h1.le
  classical
  let E := Nat.find hex
  have hE : n ≤ Nat.size (Nat.size E) := Nat.find_spec hex
  have hEmin : ∀ m, m < E → ¬ n ≤ Nat.size (Nat.size m) := fun m hm => Nat.find_min hex hm
  have hE0 : E ≠ 0 := by
    intro h0
    rw [h0] at hE
    simp at hE
    omega
  -- (ii) the budget at the threshold
  have hbud : q.eval n ≤ Nat.size E := by
    have h1 : n - 1 < Nat.size (Nat.size E) := by omega
    rw [Nat.lt_size] at h1
    have h2 := hk n
    omega
  -- one step along the chain
  have hstep : ∀ m, m < E → (zc cs (un a) m ∈ DLang ↔ zc cs (un a) (m + 1) ∈ DLang) := by
    intro m hm
    have hC : ¬ (zc cs (un a) 0).length ≤ Nat.size (Nat.size m) := by
      rw [hl]; exact hEmin m hm
    constructor
    · rintro ⟨w, -, hw⟩
      rw [RD_below _ _ _ _ hC, V_budget] at hw
      exact hbwd _ _ _ hw
    · intro hmem
      obtain ⟨w', hw'⟩ := hfwd (zc cs (un a) (m + 1)) (q.eval (n + m + 1)) (by rw [hz, Nat.add_assoc]) hmem
      have hlen : w'.length ≤ q.eval (n + m + 1) := by simpa using V_length _ _ _ _ hw'
      refine ⟨pairB w' (un (q.eval (n + m + 1))), ?_, ?_⟩
      · rw [pairB_length, un_length, hz]
        have := hroom (n + m) (by omega)
        omega
      · rw [RD_below _ _ _ _ hC, unpairB_pairB]
        exact hw'
  have hchain : ∀ m, m ≤ E → (zc cs (un a) 0 ∈ DLang ↔ zc cs (un a) m ∈ DLang) := by
    intro m
    induction m with
    | zero => intro _; exact Iff.rfl
    | succ m ih => intro hm; exact (ih (by omega)).trans (hstep m (by omega))
  -- the diagonal step
  have hdiag : zc cs (un a) E ∈ DLang ↔ ¬ zc cs (un a) 0 ∈ DLang := by
    have hC : (zc cs (un a) 0).length ≤ Nat.size (Nat.size E) := by rw [hl]; exact hE
    have hC' : ¬ (zc cs (un a) 0).length ≤ Nat.size (Nat.size (E - 1)) := by
      rw [hl]; exact hEmin _ (by omega)
    constructor
    · rintro ⟨w, -, hw⟩ hmem
      rw [RD_at _ _ _ _ hC hC'] at hw
      obtain ⟨w', hw'⟩ := hfwd (zc cs (un a) 0) (Nat.size E) (by rw [hl]; exact hbud) hmem
      rw [hw w'] at hw'
      exact Bool.noConfusion hw'
    · intro hnot
      refine ⟨[], by simp, (RD_at _ _ _ _ hC hC').2 fun w' => ?_⟩
      by_contra hV
      rw [Bool.not_eq_false] at hV
      exact hnot (hbwd _ _ _ hV)
  have h := (hchain E le_rfl).trans hdiag
  by_cases h0 : zc cs (un a) 0 ∈ DLang
  · exact (h.1 h0) h0
  · exact h0 (h.2 h0)

theorem NP_ssubset_NEXP_of (hRD : PEqualNP.Library.ComputableInPolyTime
    PEqualNP.Library.encodePair Computability.encodeBool RD) :
    PEqualNP.Library.NP ⊂ PEqualNP.Library.NEXP := by
  have hmem : DLang ∈ PEqualNP.Library.NEXP :=
    ⟨{p | RD p = true}, 2, ⟨RD, fun _ => Iff.rfl, hRD⟩, fun _ => Iff.rfl⟩
  refine ⟨PEqualNP.Library.L048, fun hsub => DLang_not_NP (hsub hmem)⟩

end PEqualNP.Library.Universal
