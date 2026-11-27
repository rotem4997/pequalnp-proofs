import PEqualNP.Library.L004
import PEqualNP.Defs.MetaComplexity
import Mathlib.Tactic

/-!
# Seeded restrictions of polynomial-time languages have small circuits

Helper for the Razborov-Rudich barrier. From the circuit of a language at input length `2 n`,
the bits of a seed `s` of length `n` are hardwired, the next `m` inputs are kept and the rest
are fixed to `false`. Two gates make the constants.
-/

namespace PEqualNP.Library.Helpers.RRSeeded

open PEqualNP.CircuitLowerBounds

/-- One step of circuit evaluation. -/
def stepf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Where wire `r` of the old circuit goes in the new one. -/
def re (n m : ℕ) (s : List Bool) (r : ℕ) : ℕ :=
  if r < n then (if s.getD r false then m else m + 1)
  else if r < n + m then r - n
  else if r < n + n then m + 1
  else r - (n + n) + m + 2

/-- A gate with its input wires renumbered. -/
def mapGate (n m : ℕ) (s : List Bool) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (re n m s)⟩

/-- The seeded circuit: constant `true`, constant `false`, then the renumbered gates. -/
def seeded (n m : ℕ) (s : List Bool) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.not, []⟩ :: ⟨GateOp.not, [m]⟩ :: C.gates.map (mapGate n m s), re n m s C.output⟩

theorem getD_snoc (l : List Bool) (b : Bool) (r : ℕ) :
    (l ++ [b]).getD r false =
      if r < l.length then l.getD r false else if r = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem re_lt (n m : ℕ) (s : List Bool) (hm : m ≤ n) (k r : ℕ) :
    (r < n + n + k ↔ re n m s r < m + 2 + k) ∧ (r = n + n + k ↔ re n m s r = m + 2 + k) := by
  unfold re
  split_ifs <;> constructor <;> constructor <;> intro h <;> omega

theorem inv_fold (n m : ℕ) (s : List Bool) (hm : m ≤ n) : ∀ (gs : List Gate) (W V : List Bool)
    (k : ℕ), W.length = n + n + k → V.length = m + 2 + k →
    (∀ r, V.getD (re n m s r) false = W.getD r false) →
    ∀ r, ((gs.map (mapGate n m s)).foldl stepf V).getD (re n m s r) false
      = (gs.foldl stepf W).getD r false := by
  intro gs
  induction gs with
  | nil => intro W V k _ _ h; simpa using h
  | cons g gs ih =>
    intro W V k hW hV h
    simp only [List.map_cons, List.foldl_cons]
    apply ih _ _ (k + 1)
    · simp [stepf, hW]; omega
    · simp [stepf, hV]; omega
    · intro r
      have hval : (mapGate n m s g).op.eval
          ((mapGate n m s g).inputs.map fun i => V.getD i false)
          = g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [mapGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      unfold stepf
      rw [getD_snoc, getD_snoc, hval, hW, hV]
      obtain ⟨h1, h2⟩ := re_lt n m s hm k r
      by_cases a : r < n + n + k
      · rw [if_pos a, if_pos (h1.1 a)]; exact h r
      · rw [if_neg a, if_neg (fun x => a (h1.2 x))]
        by_cases b : r = n + n + k
        · rw [if_pos b, if_pos (h2.1 b)]
        · rw [if_neg b, if_neg (fun x => b (h2.2 x))]

theorem tableIndex_succ {m : ℕ} (x : Fin (m + 1) → Bool) :
    PEqualNP.MetaComplexity.tableIndex x
      = (if x 0 = true then 1 else 0) + 2 * PEqualNP.MetaComplexity.tableIndex (Fin.tail x) := by
  unfold PEqualNP.MetaComplexity.tableIndex
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  have h2 : (∑ i : Fin m, if x i.succ = true then 2 ^ ((i.succ : Fin (m + 1)) : ℕ) else 0)
      = ∑ i : Fin m, 2 * (if Fin.tail x i = true then 2 ^ (i : ℕ) else 0) :=
    Finset.sum_congr rfl (fun i _ => by
      by_cases hx : x i.succ = true <;> simp [hx, Fin.tail, pow_succ, mul_comm])
  rw [h2]
  simp

theorem testBit_tableIndex : ∀ (m : ℕ) (x : Fin m → Bool) (j : ℕ),
    (PEqualNP.MetaComplexity.tableIndex x).testBit j = if h : j < m then x ⟨j, h⟩ else false := by
  intro m
  induction m with
  | zero =>
    intro x j
    simp [PEqualNP.MetaComplexity.tableIndex]
  | succ m ih =>
    intro x j
    rw [tableIndex_succ]
    cases j with
    | zero =>
      rw [dif_pos (by omega)]
      show _ = x 0
      cases hx : x 0 <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ j =>
      rw [Nat.testBit_succ]
      have e : ((if x 0 = true then 1 else 0) + 2 * PEqualNP.MetaComplexity.tableIndex (Fin.tail x)) / 2
          = PEqualNP.MetaComplexity.tableIndex (Fin.tail x) := by
        split_ifs <;> omega
      rw [e, ih]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (by omega)]; rfl
      · rw [dif_neg hj, dif_neg (by omega)]


theorem getD_app_l (l l' : List Bool) (r : ℕ) (h : r < l.length) :
    (l ++ l').getD r false = l.getD r false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left h]

theorem getD_app_r (l l' : List Bool) (r : ℕ) (h : l.length ≤ r) :
    (l ++ l').getD r false = l'.getD (r - l.length) false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right h]

theorem getD_out (l : List Bool) (r : ℕ) (h : l.length ≤ r) : l.getD r false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none h]
  rfl

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_bits {m : ℕ} (x : Fin m → Bool) (n i : ℕ) (h : i < n) :
    ((List.range n).map (fun j : ℕ => (PEqualNP.MetaComplexity.tableIndex x).testBit j)).getD i
      false = if h : i < m then x ⟨i, h⟩ else false := by
  rw [← testBit_tableIndex]
  simp [List.getD_eq_getElem?_getD, h]

theorem base_inv (n m : ℕ) (s : List Bool) (hm : m ≤ n) (hs : s.length = n)
    (x : Fin m → Bool) (r : ℕ) :
    (List.ofFn x ++ [true, false]).getD (re n m s r) false
      = (s ++ (List.range n).map
          (fun j : ℕ => (PEqualNP.MetaComplexity.tableIndex x).testBit j)).getD r false := by
  have hy : (List.ofFn x).length = m := List.length_ofFn
  unfold re
  by_cases h1 : r < n
  · rw [if_pos h1, getD_app_l s _ r (by omega)]
    cases hb : s.getD r false
    · rw [if_neg (by simp), getD_app_r (List.ofFn x) _ _ (by omega), hy]
      simp
    · rw [if_pos rfl, getD_app_r (List.ofFn x) _ _ (by omega), hy]
      simp
  · rw [if_neg h1, getD_app_r s _ r (by omega), hs]
    by_cases h2 : r < n + m
    · rw [if_pos h2, getD_app_l (List.ofFn x) _ _ (by omega), getD_ofFn x _ (by omega),
        getD_bits x n _ (by omega), dif_pos (by omega)]
    · rw [if_neg h2]
      by_cases h3 : r < n + n
      · rw [if_pos h3, getD_app_r (List.ofFn x) _ _ (by omega), hy, getD_bits x n _ (by omega),
          dif_neg (by omega)]
        simp
      · rw [if_neg h3, getD_out _ _ (by simp <;> omega), getD_out _ _ (by simp <;> omega)]

theorem two_steps {m : ℕ} (y : List Bool) (hy : y.length = m) :
    stepf (stepf y ⟨GateOp.not, []⟩) ⟨GateOp.not, [m]⟩ = y ++ [true, false] := by
  simp only [stepf, GateOp.eval, List.map_nil, List.map_cons, List.headD_nil, List.headD_cons,
    Bool.not_false]
  rw [getD_snoc, if_neg (by omega), if_pos hy.symm]
  simp

theorem bound (c' k n : ℕ) :
    c' * ((n + n) ^ k + k + (n + n) + 1) ^ 3 + 2
      ≤ (c' * (2 ^ k + k + 3) ^ 3 + 2) * (n + 1) ^ (3 * k + 3) := by
  set P := (n + 1) ^ (k + 1) with hP
  have h1 : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : (n + 1) ^ k ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : n + 1 ≤ P := by
    have := Nat.pow_le_pow_right (show 0 < n + 1 by omega) (show 1 ≤ k + 1 by omega)
    simpa using this
  have h4 : (n + n) ^ k ≤ 2 ^ k * P := by
    calc (n + n) ^ k ≤ (2 * (n + 1)) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * (n + 1) ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * P := Nat.mul_le_mul_left _ h2
  have h5 : k ≤ k * P := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : (n + n) ^ k + k + (n + n) + 1 ≤ (2 ^ k + k + 3) * P := by
    rw [add_mul, add_mul]
    omega
  have h7 : ((n + n) ^ k + k + (n + n) + 1) ^ 3 ≤ (2 ^ k + k + 3) ^ 3 * (n + 1) ^ (3 * k + 3) := by
    calc ((n + n) ^ k + k + (n + n) + 1) ^ 3 ≤ ((2 ^ k + k + 3) * P) ^ 3 :=
          Nat.pow_le_pow_left h6 3
      _ = (2 ^ k + k + 3) ^ 3 * (n + 1) ^ (3 * k + 3) := by
          rw [mul_pow, hP, ← pow_mul]
          congr 2
          ring
  have h8 : 1 ≤ (n + 1) ^ (3 * k + 3) := Nat.one_le_pow _ _ (by omega)
  have h9 := Nat.mul_le_mul_left c' h7
  rw [add_mul, mul_assoc]
  omega

theorem linkB : (∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → ∃ c : ℕ, L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n : ℕ => c * (t n + n + 1) ^ 3)) → ∀ F : Language Bool, F ∈ PEqualNP.Library.P → ∃ c d : ℕ, ∀ n m : ℕ, m ≤ n → ∀ s : List Bool, s.length = n → ∃ f : (Fin m → Bool) → Bool, PEqualNP.MetaComplexity.HasCircuitSize m f (c * (n + 1) ^ d) ∧ ∀ x : Fin m → Bool, (f x = true ↔ s ++ (List.range n).map (fun j : ℕ => (PEqualNP.MetaComplexity.tableIndex x).testBit j) ∈ F) := by
  intro H F hF
  obtain ⟨k, hk⟩ := (PEqualNP.Library.L004 F).1 hF
  obtain ⟨c', hc'⟩ := H _ F hk
  refine ⟨c' * (2 ^ k + k + 3) ^ 3 + 2, 3 * k + 3, ?_⟩
  intro n m hm s hs
  obtain ⟨C, hok, hsz, hdec⟩ := hc' (n + n)
  refine ⟨fun x => C.eval (s ++ (List.range n).map
    (fun j : ℕ => (PEqualNP.MetaComplexity.tableIndex x).testBit j)), ?_, ?_⟩
  · refine ⟨seeded n m s C, ?_, ?_, ?_⟩
    · intro g hg
      simp only [seeded, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | rfl | ⟨g0, hg0, rfl⟩
      · simp
      · simp
      · exact ⟨(hok g0 hg0).1, by simpa [mapGate] using (hok g0 hg0).2⟩
    · have : (seeded n m s C).size = C.size + 2 := by
        simp [seeded, Circuit.size]
      rw [this]
      exact le_trans (Nat.add_le_add_right hsz 2) (bound c' k n)
    · intro x
      show ((seeded n m s C).gates.foldl stepf (List.ofFn x)).getD (re n m s C.output) false
        = (C.gates.foldl stepf _).getD C.output false
      simp only [seeded, List.foldl_cons]
      rw [two_steps _ List.length_ofFn]
      apply inv_fold n m s hm C.gates _ _ 0
      · simp [hs]
      · simp
      · exact base_inv n m s hm hs x
  · intro x
    exact hdec _ (by simp [hs])

end PEqualNP.Library.Helpers.RRSeeded
