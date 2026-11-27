import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12410
open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def gs (n : ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.and, [0, n]⟩]
  | k + 1 => gs n k ++ [⟨GateOp.and, [k + 1, n + (k + 1)]⟩, ⟨GateOp.or, [2 * n + 2 * k, 2 * n + 2 * k + 1]⟩]

theorem gs_len (n : ℕ) : ∀ k, (gs n k).length = 2 * k + 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [gs, ih]; omega

theorem gs_ok (n : ℕ) : ∀ k, ∀ g ∈ gs n k,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro g hg; simp [gs] at hg; subst hg; simp
  | succ k ih =>
    intro g hg
    simp only [gs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp
    · simp

theorem gl (l : List Bool) (v : Bool) (i : ℕ) (h : i < l.length) : (l ++ [v]).getD i false = l.getD i false :=
  List.getD_append _ _ _ _ h

theorem ge (l : List Bool) (v : Bool) (k : ℕ) (h : k = l.length) : (l ++ [v]).getD k false = v := by
  subst h; simp

theorem ofg {n : ℕ} (f : Fin n → Bool) (i : ℕ) (h : i < n) : (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [h]

theorem key (n : ℕ) (x : List Bool) (hx : x.length = 2 * n) : ∀ k, k < n →
    ((gs n k).foldl stp x).length = 2 * n + 2 * k + 1 ∧
    ((gs n k).foldl stp x).getD (2 * n + 2 * k) false
      = (List.range (k + 1)).any (fun i => x.getD i false && x.getD (n + i) false) ∧
    ∀ i < 2 * n, ((gs n k).foldl stp x).getD i false = x.getD i false := by
  intro k
  induction k with
  | zero =>
    intro _
    have e : (gs n 0).foldl stp x = x ++ [x.getD 0 false && x.getD n false] := by
      simp [gs, stp, GateOp.eval]
    rw [e]
    refine ⟨by simp; omega, ?_, fun i hi => gl _ _ _ (by omega)⟩
    rw [ge _ _ _ (by omega)]
    simp
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have e : (gs n (k + 1)).foldl stp x
        = ((gs n k).foldl stp x ++ [x.getD (k + 1) false && x.getD (n + (k + 1)) false]) ++
          [((gs n k).foldl stp x).getD (2 * n + 2 * k) false ||
            (x.getD (k + 1) false && x.getD (n + (k + 1)) false)] := by
      rw [gs, List.foldl_append]
      generalize hW : (gs n k).foldl stp x = W at h1 h2 h3 ⊢
      have a1 : W.getD (k + 1) false = x.getD (k + 1) false := h3 _ (by omega)
      have a2 : W.getD (n + (k + 1)) false = x.getD (n + (k + 1)) false := h3 _ (by omega)
      simp only [List.foldl_cons, List.foldl_nil, stp, List.map_cons, List.map_nil]
      have b1 : (W ++ [GateOp.and.eval [W.getD (k + 1) false, W.getD (n + (k + 1)) false]]).getD (2 * n + 2 * k) false
          = W.getD (2 * n + 2 * k) false := gl _ _ _ (by omega)
      have b2 : (W ++ [GateOp.and.eval [W.getD (k + 1) false, W.getD (n + (k + 1)) false]]).getD (2 * n + 2 * k + 1) false
          = GateOp.and.eval [W.getD (k + 1) false, W.getD (n + (k + 1)) false] := ge _ _ _ (by omega)
      rw [b1, b2, a1, a2]
      simp [GateOp.eval]
    rw [e]
    generalize hW : (gs n k).foldl stp x = W at h1 h2 h3 ⊢
    refine ⟨by simp; omega, ?_, ?_⟩
    · rw [ge _ _ _ (by simp; omega), h2, List.range_succ (n := k + 1), List.any_append, List.any_cons, List.any_nil,
        Bool.or_false]
    · intro i hi
      rw [gl _ _ _ (by simp; omega), gl _ _ _ (by omega)]
      exact h3 i hi

theorem main : ∀ n : ℕ, ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 * n ∧
    PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C := by
  intro n
  cases n with
  | zero => exact ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], fun u => u.elim0⟩
  | succ m =>
    refine ⟨⟨gs (m + 1) m ++ [⟨GateOp.not, [2 * (m + 1) + 2 * m]⟩], 2 * (m + 1) + 2 * m + 1⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact gs_ok (m + 1) m g h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp
    · simp [Circuit.size, gs_len]; omega
    · intro u v
      have hx : (PEqualNP.Represents.oneEach u v).length = 2 * (m + 1) := by
        simp [PEqualNP.Represents.oneEach]; omega
      obtain ⟨h1, h2, _⟩ := key (m + 1) _ hx m (by omega)
      show ((gs (m + 1) m ++ [(⟨GateOp.not, [2 * (m + 1) + 2 * m]⟩ : Gate)]).foldl stp
        (PEqualNP.Represents.oneEach u v)).getD (2 * (m + 1) + 2 * m + 1) false = decide (u ≠ v)
      rw [List.foldl_append]
      generalize hW : (gs (m + 1) m).foldl stp (PEqualNP.Represents.oneEach u v) = W at h1 h2
      simp only [List.foldl_cons, List.foldl_nil, stp, List.map_cons, List.map_nil]
      rw [ge _ _ _ (by omega), h2]
      have hv : ∀ i, i < m + 1 → ((PEqualNP.Represents.oneEach u v).getD i false
          && (PEqualNP.Represents.oneEach u v).getD (m + 1 + i) false) = decide (i = u.val ∧ i = v.val) := by
        intro i hi
        have e1 : (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val) := by
          unfold PEqualNP.Represents.oneEach
          rw [List.getD_append _ _ _ _ (by simp; omega)]
          rw [ofg _ i hi]; simp [Fin.ext_iff]
        have e2 : (PEqualNP.Represents.oneEach u v).getD (m + 1 + i) false = decide (i = v.val) := by
          unfold PEqualNP.Represents.oneEach
          rw [List.getD_append_right _ _ _ _ (by simp)]
          have e : m + 1 + i - (List.ofFn fun i : Fin (m + 1) => decide (i = u)).length = i := by simp
          rw [e, ofg _ i hi]; simp [Fin.ext_iff]
        rw [e1, e2]; simp
      have hany : (List.range (m + 1)).any (fun i => (PEqualNP.Represents.oneEach u v).getD i false
          && (PEqualNP.Represents.oneEach u v).getD (m + 1 + i) false) = decide (u = v) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨i, hi, h⟩
          rw [hv i (List.mem_range.1 hi), decide_eq_true_eq] at h
          exact Fin.ext (h.1.symm.trans h.2)
        · intro h
          refine ⟨u.val, List.mem_range.2 u.isLt, ?_⟩
          rw [hv _ u.isLt, decide_eq_true_eq]
          exact ⟨rfl, by rw [h]⟩
      rw [hany]
      by_cases h : u = v <;> simp [GateOp.eval, h]

end PEqualNP.Outside.L_meta_12410

open PEqualNP.Outside.L_meta_12410 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_12410 : ∀ n : ℕ, ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 * n ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ v)) C := by
  exact main
