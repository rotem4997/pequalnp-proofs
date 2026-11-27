import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19173_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega, by rw [h6, hl]; congr 1; omega⟩

def val (n u v k : ℕ) : Bool :=
  if k = 0 then decide (u = 0 ∨ v = 0)
  else if k % 3 = 0 then decide (1 ≤ v ∧ v ≤ (k + 3) / 3)
  else if k % 3 = 1 then decide (u + (k + 3) / 3 + 1 = n ∧ 1 ≤ v ∧ v ≤ (k + 3) / 3)
  else decide (u = 0 ∨ v = 0 ∨ (n ≤ u + (k + 3) / 3 + 1 ∧ 1 ≤ v ∧ u + v + 1 ≤ n))

def f (n u v w : ℕ) : Bool :=
  if w < n then decide (u = w) else if w < 2 * n then decide (v + n = w) else val n u v (w - 2 * n)

def gate (n k : ℕ) : Gate :=
  if k = 0 then ⟨GateOp.or, [0, n]⟩
  else if k = 2 then ⟨GateOp.or, [2 * n + 0, 2 * n + 1]⟩
  else if k % 3 = 0 then ⟨GateOp.or, [if k = 3 then n + 1 else 2 * n + (k - 3), n + (k + 3) / 3]⟩
  else if k % 3 = 1 then ⟨GateOp.and, [n - 1 - (k + 3) / 3, if k = 1 then n + 1 else 2 * n + (k - 1)]⟩
  else ⟨GateOp.or, [2 * n + (k - 3), 2 * n + (k - 1)]⟩

theorem v0 (n u v : ℕ) : val n u v 0 = decide (u = 0 ∨ v = 0) := by simp [val]

theorem vQ (n u v k : ℕ) (h1 : k ≠ 0) (h2 : k % 3 = 0) :
    val n u v k = decide (1 ≤ v ∧ v ≤ (k + 3) / 3) := by simp [val, h1, h2]

theorem vA (n u v k : ℕ) (h : k % 3 = 1) :
    val n u v k = decide (u + (k + 3) / 3 + 1 = n ∧ 1 ≤ v ∧ v ≤ (k + 3) / 3) := by
  simp [val, h, show k ≠ 0 by omega]

theorem vZ (n u v k : ℕ) (h : k % 3 = 2) :
    val n u v k = decide (u = 0 ∨ v = 0 ∨ (n ≤ u + (k + 3) / 3 + 1 ∧ 1 ≤ v ∧ u + v + 1 ≤ n)) := by
  simp [val, h, show k ≠ 0 by omega]

theorem fX (n u v w : ℕ) (h : w < n) : f n u v w = decide (u = w) := by simp [f, h]

theorem fY (n u v w : ℕ) (h1 : n ≤ w) (h2 : w < 2 * n) : f n u v w = decide (v + n = w) := by
  simp [f, h2, show ¬ w < n by omega]

theorem fG (n u v k : ℕ) : f n u v (2 * n + k) = val n u v k := by
  simp [f, show ¬ 2 * n + k < n by omega]

theorem gate_ok (n u v k : ℕ) (hn : 3 ≤ n) (hk : k < 3 * n - 6) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n u v)) = f n u v (2 * n + k) := by
  unfold gate
  split_ifs with h0 h2 h3 h4 h5 h6 <;> refine ⟨by simp; omega, ?_⟩ <;>
    simp only [List.map, GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil, id,
      Bool.or_false, Bool.and_true, fG]
  · subst h0; rw [fX n u v 0 (by omega), fY n u v n le_rfl (by omega), v0]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · subst h2; rw [v0, vA n u v 1 (by norm_num), vZ n u v 2 (by norm_num)]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [fY n u v (n + 1) (by omega) (by omega), fY n u v _ (by omega) (by omega), vQ n u v k h0 h3]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [vQ n u v (k - 3) (by omega) (by omega), fY n u v _ (by omega) (by omega), vQ n u v k h0 h3]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [fX n u v _ (by omega), fY n u v (n + 1) (by omega) (by omega), vA n u v k h5]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [fX n u v _ (by omega), vQ n u v (k - 1) (by omega) (by omega), vA n u v k h5]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  · rw [vZ n u v (k - 3) (by omega), vA n u v (k - 1) (by omega), vZ n u v k (by omega)]
    apply Bool.eq_iff_iff.2; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

end PEqualNP.Outside.L_meta_19173_aux

open PEqualNP.Outside.L_meta_19173_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19173 : ∀ n : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u : ℕ) + (v : ℕ) ≤ n - 1)) (3 * n - 6) := by
  intro n hn
  refine ⟨⟨(List.range (3 * n - 6)).map (gate n), 2 * n + (3 * n - 7)⟩, ?_, by simp [Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_map, List.mem_range] at hg
    obtain ⟨k, -, rfl⟩ := hg
    unfold gate
    split_ifs <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = 2 * n := by
      simp [PEqualNP.Represents.oneEach]; omega
    have hx : ∀ i < (PEqualNP.Represents.oneEach u v).length,
        (PEqualNP.Represents.oneEach u v).getD i false = f n u v i := by
      intro i hi
      rw [hl] at hi
      apply Bool.eq_iff_iff.2
      simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD, List.getElem?_append,
        List.length_ofFn, List.getElem?_ofFn, f, val]
      split_ifs <;> simp [Fin.ext_iff] <;> omega
    show (List.foldl stp (PEqualNP.Represents.oneEach u v) ((List.range (3 * n - 6)).map (gate n))).getD (2 * n + (3 * n - 7)) false = decide ((u : ℕ) + (v : ℕ) ≤ n - 1)
    rw [spec (f n u v) _ _ hx (fun k hk => by
      simp only [List.length_map, List.length_range] at hk
      simp only [List.getElem_map, List.getElem_range, hl]
      exact gate_ok n u v k hn hk) _ (by simp [hl]; omega), fG, vZ n u v _ (by omega)]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    omega
