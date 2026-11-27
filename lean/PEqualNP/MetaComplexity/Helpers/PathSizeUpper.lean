import PEqualNP.MetaComplexity.Helpers.PathSizeLower
import PEqualNP.MetaComplexity.Helpers.OrChain

/-!
# The path function: the upper bound, and the exact size

Helper for `L-meta-102`. A gate list at an arbitrary wire offset computes the path function on
the first `n` wires with `n + n / 2 - 2` gates (`n ≥ 2`): one AND gate for `n = 2`, two gates
for `n = 3`, and three more gates from `n` to `n + 2`:
`path (n + 2) = path n OR (x n AND (x (n - 1) OR x (n + 1)))`.
-/

namespace PEqualNP.MetaComplexity.Helpers.PathSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

/-- The path function on the first `n` entries of a wire list. -/
def pathB (w : List Bool) : ℕ → Bool
  | 0 => false
  | 1 => false
  | k + 2 => pathB w (k + 1) || (w.getD k false && w.getD (k + 1) false)

theorem pathB_iff (w : List Bool) : ∀ n : ℕ, pathB w n = true ↔
    ∃ i, i + 1 < n ∧ w.getD i false = true ∧ w.getD (i + 1) false = true
  | 0 => by simp [pathB]
  | 1 => by simp [pathB]
  | k + 2 => by
    rw [pathB, Bool.or_eq_true, pathB_iff w (k + 1), Bool.and_eq_true]
    constructor
    · rintro (⟨i, hi, h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨i, by omega, h1, h2⟩
      · exact ⟨k, by omega, h1, h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      by_cases hik : i = k
      · subst hik; exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨i, by omega, h1, h2⟩

theorem pathB_step (w : List Bool) (n : ℕ) (hn : 1 ≤ n) :
    pathB w (n + 2) = (pathB w n ||
      (w.getD n false && (w.getD (n - 1) false || w.getD (n + 1) false))) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [pathB, Nat.add_sub_cancel]
  generalize pathB w (n + 1) = P
  generalize w.getD n false = a
  generalize w.getD (n + 1) false = b
  generalize w.getD (n + 1 + 1) false = c
  cases P <;> cases a <;> cases b <;> cases c <;> rfl

theorem three_gates (v : List Bool) (a b c o : ℕ) (ha : a < v.length) (hb : b < v.length)
    (hc : c < v.length) (ho : o < v.length) :
    (wiresFrom [⟨GateOp.or, [a, c]⟩, ⟨GateOp.and, [b, v.length]⟩,
      ⟨GateOp.or, [o, v.length + 1]⟩] v).getD (v.length + 2) false
      = (v.getD o false || (v.getD b false && (v.getD a false || v.getD c false))) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length →
      (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ ha, A _ _ hb, A _ _ hc, A _ _ ho]

theorem pathGates : ∀ n : ℕ, 2 ≤ n → ∀ m : ℕ, n ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 2 = n + n / 2 ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m → (wiresFrom gs w).getD out false = pathB w n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn m hm
    match n, hn, hm, ih with
    | 2, _, hm, _ =>
      refine ⟨[⟨GateOp.and, [0, 1]⟩], m, ?_, rfl, by simp, ?_⟩
      · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp [Ok]
      · intro w hw
        have A : ∀ (t : List Bool) (i : ℕ), i < w.length →
            (w ++ t)[i]?.getD false = w[i]?.getD false := by
          intro t i h; rw [List.getElem?_append_left h]
        subst hw
        simp [wiresFrom, GateOp.eval, pathB, A _ 0 (by omega), A _ 1 (by omega)]
    | 3, _, hm, _ =>
      refine ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, m]⟩], m + 1, ?_, rfl, by simp, ?_⟩
      · intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl <;> simp [Ok]
      · intro w hw
        have A : ∀ (t : List Bool) (i : ℕ), i < w.length →
            (w ++ t)[i]?.getD false = w[i]?.getD false := by
          intro t i h; rw [List.getElem?_append_left h]
        subst hw
        simp [wiresFrom, GateOp.eval, pathB, A _ 0 (by omega), A _ 1 (by omega),
          A _ 2 (by omega)]
        generalize w[0]?.getD false = a
        generalize w[1]?.getD false = b
        generalize w[2]?.getD false = c
        cases a <;> cases b <;> cases c <;> simp
    | n + 4, _, hm, ih =>
      obtain ⟨gs, out, ok, len, hout, ev⟩ := ih (n + 2) (by omega) (by omega) m (by omega)
      refine ⟨gs ++ [⟨GateOp.or, [n + 1, n + 3]⟩, ⟨GateOp.and, [n + 2, m + gs.length]⟩,
        ⟨GateOp.or, [out, m + gs.length + 1]⟩], m + gs.length + 2, ?_, ?_, by simp; omega, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact ok g hg
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl | rfl <;> simp [Ok]
      · simp only [List.length_append, List.length_cons, List.length_nil]
        have : (n + 4) / 2 = (n + 2) / 2 + 1 := by omega
        omega
      · intro w hw
        rw [wiresFrom_append]
        set v := wiresFrom gs w with hv
        have lv : v.length = m + gs.length := by rw [hv, length_wiresFrom, hw]
        have e : ∀ i, i < m → v.getD i false = w.getD i false := by
          intro i hi; rw [hv, getD_wiresFrom _ _ _ (by omega)]
        rw [← lv, three_gates v _ _ _ _ (by omega) (by omega) (by omega) (by omega),
          e (n + 1) (by omega), e (n + 2) (by omega), e (n + 3) (by omega), hv, ev w hw,
          pathB_step w (n + 2) (by omega)]
        rfl

theorem getD_ofFn_ext {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = ext x i := by
  unfold ext
  by_cases hi : i < n
  · rw [dif_pos hi]; simp [hi]
  · rw [dif_neg hi, List.getD_eq_default _ _ (by simp; omega)]

theorem pathB_ofFn {n : ℕ} (x : Fin n → Bool) : pathB (List.ofFn x) n = path n x := by
  rw [path_eq_G, Bool.eq_iff_iff, pathB_iff, G_iff]
  simp only [getD_ofFn_ext]
  constructor
  · rintro ⟨i, _, h1, h2⟩
    exact Or.inr ⟨i, Nat.zero_le _, h1, h2⟩
  · rintro (⟨i, hi, _⟩ | ⟨i, _, h1, h2⟩)
    · omega
    · exact ⟨i, ext_lt h2, h1, h2⟩

theorem path_upper (n s : ℕ) (h : n + n / 2 ≤ s + 2) : HasCircuitSize n (path n) s := by
  by_cases hn : n ≤ 1
  · refine ⟨⟨[], n⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
    intro x
    have hp : path n x = false := by
      rw [← Bool.not_eq_true, path, decide_eq_true_iff]
      rintro ⟨i, j, hij, _, _⟩
      have := j.2; omega
    rw [hp]
    simp [Circuit.eval, Circuit.wires]
  · obtain ⟨gs, out, ok, len, _, ev⟩ := pathGates n (by omega) n le_rfl
    refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    simp only [Circuit.eval, wires_eq, ev (List.ofFn x) (by simp), pathB_ofFn]

/-- The path function on `n` inputs has a circuit with `s` gates exactly when
`n + n / 2 ≤ s + 2`. -/
theorem path_size (n s : ℕ) :
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) s ↔
      n + n / 2 ≤ s + 2 :=
  ⟨path_lower n s, path_upper n s⟩

end PEqualNP.MetaComplexity.Helpers.PathSize
