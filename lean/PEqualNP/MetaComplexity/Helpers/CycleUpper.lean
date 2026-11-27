import PEqualNP.MetaComplexity.Helpers.CyclePathGates

/-!
# The cycle function: upper bound, restrictions, and the assembly for L-meta-106

Helper for `L-meta-106` (proofs only, no statement may use it). The cycle function on `n`
inputs is true when two cyclically consecutive inputs are both true. This file proves:

* rotation invariance, and the reduction of "input `v` fixed" to "the last input fixed";
* the upper bound `n + (n + 1) / 2 - 1` gates for `n ≥ 2`, by the path on the first `n - 1`
  inputs and one more centre at input `n - 1`;
* the two restriction identities at the last input (value `false`: the path on `n - 1`
  inputs; value `true`: the class `G (n - 1) 2` after a renaming) and the size bounds they
  give from `path_lower` and `G_lower`;
* the arithmetic of the final step, and the exact size conditional on `StmtCycCore`, the
  gate-elimination core that is still open.
-/

namespace PEqualNP.MetaComplexity.Helpers.CycleSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.MetaComplexity.Helpers.PathSize
open PEqualNP.MetaComplexity.Helpers.CycleSize.PG

/-- The cycle function of `L-meta-106`, verbatim. -/
def cyc (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x : Fin n → Bool => decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)

theorem succ_mod_eq {i n : ℕ} (h : i < n) : (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  split_ifs with h1
  · rw [h1, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cycle function read at natural indices. -/
theorem cyc_iff_ext (n : ℕ) (x : Fin n → Bool) : cyc n x = true ↔
    ∃ i, i < n ∧ ext x i = true ∧ ext x (if i + 1 = n then 0 else i + 1) = true := by
  unfold cyc
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨i.val, i.2, by rw [ext_fin]; exact hi, ?_⟩
    rw [← succ_mod_eq i.2, hij, ext_fin]; exact hj
  · rintro ⟨i, hi, h1, h2⟩
    have hl := ext_lt h2
    refine ⟨⟨i, hi⟩, ⟨_, hl⟩, succ_mod_eq hi, ?_, ?_⟩
    · rw [← ext_fin x ⟨i, hi⟩]; exact h1
    · rw [← ext_fin x ⟨_, hl⟩]; exact h2

/-! ## Rotation -/

/-- The rotation `i ↦ (i + c) mod n`. -/
def rot (n c : ℕ) (i : Fin n) : Fin n := ⟨(i.val + c) % n, Nat.mod_lt _ (by have := i.2; omega)⟩

theorem cyc_rot_imp (n c : ℕ) (x : Fin n → Bool) (h : cyc n (x ∘ rot n c) = true) :
    cyc n x = true := by
  unfold cyc at h ⊢
  rw [decide_eq_true_iff] at h ⊢
  obtain ⟨i, j, hij, hi, hj⟩ := h
  refine ⟨rot n c i, rot n c j, ?_, hi, hj⟩
  simp only [rot]
  rw [Nat.mod_add_mod, ← hij, Nat.mod_add_mod]
  congr 1; omega

theorem rot_inv (n c : ℕ) (hc : c ≤ n) (i : Fin n) : rot n c (rot n (n - c) i) = i := by
  apply Fin.ext
  simp only [rot]
  rw [Nat.mod_add_mod, show i.val + (n - c) + c = i.val + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.2]

/-- The cycle function is invariant under every rotation of its inputs. -/
theorem cyc_rot (n c : ℕ) (hc : c ≤ n) (x : Fin n → Bool) : cyc n (x ∘ rot n c) = cyc n x := by
  rw [Bool.eq_iff_iff]
  refine ⟨cyc_rot_imp n c x, fun h => cyc_rot_imp n (n - c) (x ∘ rot n c) ?_⟩
  have e : (x ∘ rot n c) ∘ rot n (n - c) = x := by
    funext i; simp only [Function.comp_apply, rot_inv n c hc]
  rw [e]; exact h

/-! ## The upper bound -/

theorem cyc_eq_path_or (m : ℕ) (hm : 2 ≤ m) (x : Fin (m + 1) → Bool) :
    cyc (m + 1) x = (pathB (List.ofFn x) m ||
      (ext x m && (ext x (m - 1) || ext x 0))) := by
  rw [Bool.eq_iff_iff, cyc_iff_ext, Bool.or_eq_true, pathB_iff, Bool.and_eq_true,
    Bool.or_eq_true]
  simp only [getD_ofFn_ext]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    by_cases h3 : i + 1 < m
    · rw [if_neg (by omega)] at h2
      exact Or.inl ⟨i, h3, h1, h2⟩
    · by_cases h4 : i = m
      · subst h4; rw [if_pos rfl] at h2
        exact Or.inr ⟨h1, Or.inr h2⟩
      · rw [if_neg (by omega), show i + 1 = m by omega] at h2
        rw [show i = m - 1 by omega] at h1
        exact Or.inr ⟨h2, Or.inl h1⟩
  · rintro (⟨i, hi, h1, h2⟩ | ⟨h1, h2 | h2⟩)
    · exact ⟨i, by omega, h1, by rw [if_neg (by omega)]; exact h2⟩
    · exact ⟨m - 1, by omega, h2, by rw [if_neg (by omega), show m - 1 + 1 = m by omega]; exact h1⟩
    · exact ⟨m, by omega, h1, by rw [if_pos rfl]; exact h2⟩

/-- The upper bound: `n + (n + 1) / 2 - 1` gates for the cycle function, `n ≥ 3`. -/
theorem cyc_upper (n s : ℕ) (hn : 3 ≤ n) (h : n + (n + 1) / 2 ≤ s + 1) :
    HasCircuitSize n (cyc n) s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨gs, out, ok, len, hout, ev⟩ := pathGates m (by omega) (m + 1) (by omega)
  refine ⟨⟨gs ++ [⟨GateOp.or, [m - 1, 0]⟩, ⟨GateOp.and, [m, m + 1 + gs.length]⟩,
    ⟨GateOp.or, [out, m + 1 + gs.length + 1]⟩], m + 1 + gs.length + 2⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact ok g hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp [Ok]
  · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro x
    simp only [Circuit.eval, wires_eq]
    rw [wiresFrom_append]
    set w := List.ofFn x with hw
    have hwl : w.length = m + 1 := by simp [hw]
    set v := wiresFrom gs w with hv
    have lv : v.length = m + 1 + gs.length := by rw [hv, length_wiresFrom, hwl]
    have e : ∀ i, i < m + 1 → v.getD i false = w.getD i false := by
      intro i hi; rw [hv, getD_wiresFrom _ _ _ (by omega)]
    rw [← lv, three_gates v _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      e (m - 1) (by omega), e m (by omega), e 0 (by omega), hv, ev w hwl,
      cyc_eq_path_or m (by omega) x, hw]
    simp only [getD_ofFn_ext]

/-! ## The two restriction identities at the last input -/

theorem ext_snoc (m : ℕ) (y : Fin m → Bool) (b : Bool) (j : ℕ) :
    ext (Fin.snoc y b : Fin (m + 1) → Bool) j =
      if j < m then ext y j else if j = m then b else false := by
  unfold ext
  by_cases h1 : j < m
  · rw [dif_pos (by omega), if_pos h1, dif_pos h1]
    simp [Fin.snoc, h1]
  · rw [if_neg h1]
    by_cases h2 : j = m
    · subst h2; rw [dif_pos (by omega), if_pos rfl]
      simp [Fin.snoc]
    · rw [dif_neg (by omega), if_neg h2]

/-- Value `false` at the last input: the path on the other `n - 1` inputs. -/
theorem cyc_snoc_false (m : ℕ) (y : Fin m → Bool) :
    cyc (m + 1) (Fin.snoc y false) = path m y := by
  rw [Bool.eq_iff_iff, cyc_iff_ext, path_eq_G, G_iff]
  simp only [ext_snoc]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    by_cases a : i + 1 < m
    · simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] at h1 h2
      exact Or.inr ⟨i, Nat.zero_le _, h1, h2⟩
    · by_cases b : i = m
      · subst b; simp at h1
      · simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] at h2
        simp at h2
  · rintro (⟨i, hi, _⟩ | ⟨i, _, h1, h2⟩)
    · omega
    · have := ext_lt h2
      refine ⟨i, by omega, ?_, ?_⟩ <;> simp (disch := omega) only [if_pos, if_neg, ite_true, ite_false] <;> assumption

/-- The renaming for value `true`: `0 ↦ 0`, `m - 1 ↦ 1`, `k ↦ k + 1` otherwise. -/
def tauN (m j : ℕ) : ℕ := if j = 0 then 0 else if j + 1 = m then 1 else j + 1

def tau (m : ℕ) (j : Fin m) : Fin m := ⟨tauN m j.val % m, Nat.mod_lt _ (by have := j.2; omega)⟩

theorem ext_tau (m : ℕ) (hm : 2 ≤ m) (z : Fin m → Bool) (j : ℕ) :
    ext (z ∘ tau m) j = if j < m then ext z (tauN m j) else false := by
  unfold ext
  by_cases h1 : j < m
  · have ht : tauN m j < m := by unfold tauN; split_ifs <;> omega
    rw [dif_pos h1, if_pos h1, dif_pos ht]
    simp only [Function.comp_apply, tau, Nat.mod_eq_of_lt ht]
  · rw [dif_neg h1, if_neg h1]

/-- Value `true` at the last input: after the renaming `tau`, two free OR inputs and a path
on the other `n - 3` inputs, the class `G (n - 1) 2`. -/
theorem cyc_snoc_true (m : ℕ) (hm : 3 ≤ m) (z : Fin m → Bool) :
    cyc (m + 1) (Fin.snoc (z ∘ tau m) true) = G m 2 z := by
  rw [Bool.eq_iff_iff, cyc_iff_ext, G_iff]
  simp only [ext_snoc, ext_tau m (by omega)]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    by_cases h3 : i = m
    · subst h3
      simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h2
      exact Or.inl ⟨0, by omega, h2⟩
    · by_cases h4 : i + 1 = m
      · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h1
        exact Or.inl ⟨1, by omega, h1⟩
      · by_cases h5 : i = 0
        · subst h5
          simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h1
          exact Or.inl ⟨0, by omega, h1⟩
        · by_cases h6 : i + 2 = m
          · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h2
            exact Or.inl ⟨1, by omega, h2⟩
          · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] at h1 h2
            exact Or.inr ⟨i + 1, by omega, h1, h2⟩
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h1, h2⟩)
    · by_cases h0 : i = 0
      · subst h0
        refine ⟨m, by omega, ?_, ?_⟩ <;>
          simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false] <;> assumption
      · have h1 : i = 1 := by omega
        subst h1
        refine ⟨m - 1, by omega, ?_, ?_⟩
        · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false]; exact h
        · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false, show m - 1 + 1 = m by omega]
    · have hl := ext_lt h2
      refine ⟨i - 1, by omega, ?_, ?_⟩
      · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false, show i - 1 + 1 = i by omega]
        exact h1
      · simp (disch := omega) only [tauN, if_pos, if_neg, ite_true, ite_false, show i - 1 + 1 = i by omega]
        exact h2

/-! ## Size bounds for the two restrictions, from the checked path bounds -/

/-- (a') Value `false` at the last input: `(n - 1) + (n - 1) / 2 ≤ s + 2`, with `n = m + 1`. -/
theorem cyc_false_lower (m s : ℕ)
    (h : HasCircuitSize m (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y false)) s) :
    m + m / 2 ≤ s + 2 := by
  have e : (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y false)) = path m :=
    funext (cyc_snoc_false m)
  rw [e] at h
  exact path_lower m s h

/-- (b') Value `true` at the last input: `(n - 1) + (n - 3) / 2 ≤ s + 2`, with `n = m + 1`. -/
theorem cyc_true_lower (m s : ℕ) (hm : 4 ≤ m)
    (h : HasCircuitSize m (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y true)) s) :
    m + (m - 2) / 2 ≤ s + 2 := by
  have h' := relabel_size (tau m) _ s h
  have e : (fun x : Fin m → Bool =>
      (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y true)) (x ∘ tau m)) = G m 2 :=
    funext fun z => cyc_snoc_true m (by omega) z
  rw [e] at h'
  exact G_lower (m - 2) (by omega) 2 m s (by omega) h'

/-! ## From "input `v` fixed" to "the last input fixed" -/

/-- The renaming that undoes the rotation taking the last input to `v`. -/
def piv (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (i : Fin (m + 1)) : Fin m :=
  ⟨((i.val + (m - v.val)) % (m + 1)) % m, Nat.mod_lt _ hm⟩

/-- A circuit for the cycle function with input `v` fixed to `b` (arity kept, the form
`gate_elim_at` produces) gives one of the same size with the last input fixed to `b` and
dropped. -/
theorem restrict_last (m : ℕ) (hm : 0 < m) (v : Fin (m + 1)) (b : Bool) (s : ℕ)
    (h : HasCircuitSize (m + 1) (fun x => cyc (m + 1) (Function.update x v b)) s) :
    HasCircuitSize m (fun y : Fin m → Bool => cyc (m + 1) (Fin.snoc y b)) s := by
  have h' := relabel_size (piv m hm v) _ s h
  have e : (fun y : Fin m → Bool =>
      (fun x => cyc (m + 1) (Function.update x v b)) (y ∘ piv m hm v))
      = fun y => cyc (m + 1) (Fin.snoc y b) := by
    funext y
    simp only
    rw [← cyc_rot (m + 1) (v.val + 1) (by omega) (Function.update (y ∘ piv m hm v) v b)]
    congr 1
    funext i
    induction i using Fin.lastCases with
    | last =>
      have hl : rot (m + 1) (v.val + 1) (Fin.last m) = v := by
        apply Fin.ext
        simp only [rot, Fin.val_last]
        rw [show m + (v.val + 1) = v.val + (m + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt v.2]
      simp only [Function.comp_apply, hl, Function.update_self, Fin.snoc_last]
    | cast j =>
      have hj := j.2
      have hv := v.2
      have hne : rot (m + 1) (v.val + 1) j.castSucc ≠ v := by
        intro hc
        have h0 := congrArg Fin.val hc
        simp only [rot, Fin.val_castSucc] at h0
        rcases lt_or_ge (j.val + (v.val + 1)) (m + 1) with h1 | h1
        · rw [Nat.mod_eq_of_lt h1] at h0; omega
        · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)] at h0; omega
      have hp : piv m hm v (rot (m + 1) (v.val + 1) j.castSucc) = j := by
        apply Fin.ext
        simp only [piv, rot, Fin.val_castSucc]
        rw [Nat.mod_add_mod, show j.val + (v.val + 1) + (m - v.val) = j.val + (m + 1) by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : j.val < m + 1), Nat.mod_eq_of_lt hj]
      simp only [Function.comp_apply, Function.update_of_ne hne, hp, Fin.snoc_castSucc]
  rw [e] at h'
  exact h'

/-! ## The arithmetic of the last step -/

/-- Below the claimed size, the value-`false` bound (a') fails at `s - 3`. -/
theorem arith_false (n s : ℕ) (hn : 5 ≤ n) (hs : s + 1 < n + (n + 1) / 2) (h3 : 3 ≤ s) :
    ¬ ((n - 1) + (n - 1) / 2 ≤ (s - 3) + 2) := by
  omega

/-- Below the claimed size, the value-`true` bound (b') fails at `s - 4`. -/
theorem arith_true (n s : ℕ) (hn : 5 ≤ n) (hs : s + 1 < n + (n + 1) / 2) (h4 : 4 ≤ s) :
    ¬ ((n - 1) + (n - 3) / 2 ≤ (s - 4) + 2) := by
  omega

/-! ## The open core and the conditional exact size -/

/-- The one missing fact (the gate-elimination core): below the claimed size, some input `v`
can be fixed to `false` saving three gates, or to `true` saving four, the arity kept. -/
def StmtCycCore : Prop :=
  ∀ n s : ℕ, 5 ≤ n → s + 1 < n + (n + 1) / 2 → HasCircuitSize n (cyc n) s →
    ∃ v : Fin n,
      (3 ≤ s ∧ HasCircuitSize n (fun x => cyc n (Function.update x v false)) (s - 3)) ∨
      (4 ≤ s ∧ HasCircuitSize n (fun x => cyc n (Function.update x v true)) (s - 4))

/-- `L-meta-106` from the core. -/
theorem cyc_exact_of_core (hcore : StmtCycCore) :
    ∀ n s : ℕ, 5 ≤ n → (PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧ x i = true ∧ x j = true)) s ↔
      n + (n + 1) / 2 ≤ s + 1) := by
  intro n s hn
  constructor
  · intro h
    by_contra hlt
    have hs : s + 1 < n + (n + 1) / 2 := by omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨v, ⟨h3, hc⟩ | ⟨h4, hc⟩⟩ := hcore (m + 1) s hn hs h
    · have := cyc_false_lower m (s - 3) (restrict_last m (by omega) v false (s - 3) hc)
      exact arith_false (m + 1) s hn hs h3 (by simpa using this)
    · have := cyc_true_lower m (s - 4) (by omega) (restrict_last m (by omega) v true (s - 4) hc)
      exact arith_true (m + 1) s hn hs h4 (by omega)
  · exact cyc_upper n s (by omega)

end PEqualNP.MetaComplexity.Helpers.CycleSize
