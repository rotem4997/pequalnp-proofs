import PEqualNP.MetaComplexity.Helpers.Parity4

/-!
# The parity upper bound, importable together with the lower bound

`Helpers/OrChain.lean` and `Helpers/Parity3.lean` both declare `Helpers.getD_ofFn`, so
`L-meta-026` (upper bound) and `L-meta-031` (lower bound) cannot be imported in one module, and
neither helper may be edited (checked lemmas rest on them). This file proves the upper bound
again on the `Parity3` side under new names; nothing here changes an existing declaration.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds

theorem par_succ_getD_alt (k : ℕ) (w : List Bool) :
    par (k + 2) (fun i : Fin (k + 2) => w.getD i false)
      = xor (par (k + 1) (fun i : Fin (k + 1) => w.getD i false)) (w.getD (k + 1) false) := by
  have h := par_snoc (k + 1) (fun i : Fin (k + 1) => w.getD i false) (w.getD (k + 1) false)
  have e : (Fin.snoc (fun i : Fin (k + 1) => w.getD i false) (w.getD (k + 1) false)
      : Fin (k + 2) → Bool) = fun i : Fin (k + 2) => w.getD i false := by
    have := Fin.snoc_init_self (fun i : Fin (k + 2) => w.getD i false)
    exact this
  rw [e] at h
  exact h

theorem par_one_alt (x : Fin 1 → Bool) : par 1 x = x 0 := by
  unfold par
  rw [Finset.card_filter, Fin.sum_univ_one]
  cases x 0 <;> simp

/-- The four gates of one exclusive or, appended to the wires `v`: with `a = v[i]` and
`b = v[j]` they produce `(a or b) and not (a and b)` on the last wire. -/
theorem xorStepAlt (v : List Bool) (i j : ℕ) (hi : i < v.length) (hj : j < v.length) :
    (wiresFrom [⟨GateOp.or, [i, j]⟩, ⟨GateOp.and, [i, j]⟩, ⟨GateOp.not, [v.length + 1]⟩,
      ⟨GateOp.and, [v.length, v.length + 2]⟩] v).getD (v.length + 3) false
      = xor (v.getD i false) (v.getD j false) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hi, A _ _ hj]
  cases v[i]?.getD false <;> cases v[j]?.getD false <;> rfl

theorem xorChainAlt (k : ℕ) : ∀ m : ℕ, k + 1 ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = 4 * k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = par (k + 1) (fun i : Fin (k + 1) => w.getD i false) := by
  induction k with
  | zero =>
    intro m hm
    refine ⟨[], 0, by simp, rfl, by simp; omega, ?_⟩
    intro w _
    rw [par_one_alt]
    rfl
  | succ k ih =>
    intro m hm
    obtain ⟨gs, out, ok, len, hout, ev⟩ := ih m (by omega)
    refine ⟨gs ++ [⟨GateOp.or, [out, k + 1]⟩, ⟨GateOp.and, [out, k + 1]⟩,
      ⟨GateOp.not, [m + gs.length + 1]⟩, ⟨GateOp.and, [m + gs.length, m + gs.length + 2]⟩],
      m + gs.length + 3, ?_, by simp [len]; omega, by simp; omega, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ok g hg
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;> simp [Ok]
    · intro w hw
      rw [wiresFrom_append]
      have lv : (wiresFrom gs w).length = m + gs.length := by rw [length_wiresFrom, hw]
      have e1 : (wiresFrom gs w).getD (k + 1) false = w.getD (k + 1) false :=
        getD_wiresFrom _ _ _ (by omega)
      rw [par_succ_getD_alt, ← ev w hw, ← e1, ← lv]
      exact xorStepAlt _ _ _ (by omega) (by omega)

/-- The statement of `L-meta-026`, importable next to `L-meta-031`. -/
theorem parity_upper_alt : ∀ n : ℕ,
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) (4 * (n - 1)) := by
  intro n
  cases n with
  | zero =>
    refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
    intro x
    simp [Circuit.eval, Circuit.wires]
  | succ k =>
    obtain ⟨gs, out, ok, len, _, ev⟩ :=
      xorChainAlt k (k + 1) le_rfl
    refine ⟨⟨gs, out⟩, ok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have h := ev (List.ofFn x) (by simp)
    simp only [Circuit.eval,
      wires_eq, h, getD_ofFn]
    rfl

end PEqualNP.MetaComplexity.Helpers
