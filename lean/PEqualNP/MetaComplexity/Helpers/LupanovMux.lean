import PEqualNP.MetaComplexity.Helpers.Shannon

/-!
# The multiplexer level of the two-level construction

Helper for `L-meta-003`. Given library wires `idx g` that carry every function `g` of the first
`k` variables, a function of `k + j` variables is computed by Shannon expansion on the last `j`
variables. The base case (`j = 0`) costs no gate: its output is a library wire.
-/

namespace PEqualNP.MetaComplexity.Helpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem lupanovMux (k : ℕ) (idx : ((Fin k → Bool) → Bool) → ℕ) :
    ∀ (j : ℕ) (f : (Fin (k + j) → Bool) → Bool) (m : ℕ), k + j ≤ m → (∀ g, idx g < m) →
      ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 4 * 2 ^ j ∧
        out < m + gs.length ∧
        ∀ w : List Bool, w.length = m →
          (∀ g : (Fin k → Bool) → Bool, w.getD (idx g) false = g (fun i : Fin k => w.getD i false)) →
          (wiresFrom gs w).getD out false = f (fun i : Fin (k + j) => w.getD i false) := by
  intro j
  induction j with
  | zero =>
    intro f m _ hidx
    refine ⟨[], idx f, by simp, by simp, by simpa using hidx f, ?_⟩
    intro w _ hw
    simpa [wiresFrom] using hw f
  | succ j ih =>
    intro f m hm hidx
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega) hidx
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
        (fun g => by have := hidx g; omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k + j]⟩, ⟨GateOp.and, [M, o0]⟩,
      ⟨GateOp.and, [k + j, o1]⟩, ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw hlib
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have hlib1 : ∀ g : (Fin k → Bool) → Bool,
          w1.getD (idx g) false = g (fun i : Fin k => w1.getD i false) := by
        intro g
        have hg := hidx g
        rw [hw1, getD_wiresFrom _ _ _ (by omega), hlib g]
        congr 1; funext i
        exact (getD_wiresFrom _ _ _ (by have := i.isLt; omega)).symm
      have e0 : w2.getD o0 false
          = f (Fin.snoc (fun i : Fin (k + j) => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw hlib
      have e1 : w2.getD o1 false
          = f (Fin.snoc (fun i : Fin (k + j) => w.getD i false) true) := by
        rw [ev1 w1 l1 hlib1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD (k + j) false = w.getD (k + j) false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + (j + 1)) => w.getD i false)
          = Fin.snoc (fun i : Fin (k + j) => w.getD i false) (w.getD (k + j) false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k + j < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 (k + j) o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD (k + j) false <;> simp

end PEqualNP.MetaComplexity.Helpers
