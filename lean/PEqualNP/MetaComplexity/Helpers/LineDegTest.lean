import PEqualNP.Defs.LineDegree
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The test lemma for line-degree (helper for L-meta-629)

An AND/OR circuit of line-degree at most `D` that is true on every edge input and false on every
input "a set `S` of at most `D` lines plus all points adjacent to no line of `S`" computes the
edge function. Proof: monotonicity of the wires, and the invariant that a true wire of degree
`d` at `x` stays true at `x` with all but at most `d` of its true lines switched off.
-/

namespace PEqualNP.MetaComplexity.LineDegTest

open PEqualNP.CircuitLowerBounds

/-- The wires after the gates `gs`, on input `x`. -/
def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

/-- The line-degrees after the gates `gs`. -/
def Dg (gs : List Gate) (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d])
    ((List.range n).map fun i => if i ∈ marked then 1 else 0)

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem Dg_snoc (gs : List Gate) (g : Gate) (n : ℕ) (marked : Finset ℕ) :
    Dg (gs ++ [g]) n marked = Dg gs n marked ++ [g.lineDegree (Dg gs n marked)] := by
  simp [Dg, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem Dg_length (gs : List Gate) (n : ℕ) (marked : Finset ℕ) :
    (Dg gs n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton gs g ih => rw [Dg_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

/-- Pointwise order on bit lists, read through `getD`. -/
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

/-- `x` with every marked position outside `T` set false. -/
def rst (marked T : Finset ℕ) (x : List Bool) : List Bool :=
  x.mapIdx fun i b => b && (decide (i ∉ marked) || decide (i ∈ T))

theorem rst_length (marked T : Finset ℕ) (x : List Bool) : (rst marked T x).length = x.length := by
  simp [rst]

theorem rst_getD (marked T : Finset ℕ) (x : List Bool) (i : ℕ) :
    (rst marked T x).getD i false =
      (x.getD i false && (decide (i ∉ marked) || decide (i ∈ T))) := by
  simp only [rst, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases x[i]? <;> simp

theorem rst_mono (marked : Finset ℕ) {T U : Finset ℕ} (hTU : T ⊆ U) (x : List Bool) :
    Le (rst marked T x) (rst marked U x) := by
  intro i h
  rw [rst_getD] at h ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨h.1, h.2.imp id (fun hi => hTU hi)⟩

/-- The marked positions true in `x`. -/
def lines (marked : Finset ℕ) (x : List Bool) : Finset ℕ :=
  (Finset.range x.length).filter fun i => i ∈ marked ∧ x.getD i false = true

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The invariant: a true wire of degree `d` at `x` is true at `x` restricted to at most `d` of
its true lines. -/
theorem inv (marked : Finset ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (n : ℕ) (x : List Bool)
    (hx : x.length = n) : ∀ t, (W gs x).getD t false = true →
      ∃ T ⊆ lines marked x, T.card ≤ (Dg gs n marked).getD t 0 ∧
        (W gs (rst marked T x)).getD t false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    simp only [W, List.foldl_nil] at ht ⊢
    have htl := getD_false_lt ht
    have hdeg : (Dg [] n marked).getD t 0 = if t ∈ marked then 1 else 0 := by
      simp [Dg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, ← hx, htl]
    rw [hdeg]
    by_cases hmk : t ∈ marked
    · refine ⟨{t}, ?_, by simp [hmk], ?_⟩
      · intro i hi; rw [Finset.mem_singleton] at hi; subst hi
        simp only [lines, Finset.mem_filter, Finset.mem_range]; exact ⟨htl, hmk, ht⟩
      · rw [rst_getD, ht]; simp
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      rw [rst_getD, ht]; simp [hmk]
  | append_singleton gs g ih =>
    have hm' : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hm g' (by simp [hg'])
    have ih := ih hm'
    have hlenW : ∀ T, (W gs (rst marked T x)).length = (W gs x).length := by
      intro T; simp [W_length, rst_length]
    have hlenD : (Dg gs n marked).length = (W gs x).length := by
      simp [W_length, Dg_length, hx]
    intro t ht
    rw [W_snoc, getD_snoc] at ht
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht
      obtain ⟨T, hTL, hTc, hTv⟩ := ih t ht
      refine ⟨T, hTL, ?_, ?_⟩
      · rw [Dg_snoc, getD_snoc, if_pos (by rw [hlenD]; exact h1)]; exact hTc
      · rw [W_snoc, getD_snoc, if_pos (by rw [hlenW]; exact h1)]; exact hTv
    rw [if_neg h1] at ht
    by_cases h2 : t = (W gs x).length
    swap
    · rw [if_neg h2] at ht; simp at ht
    rw [if_pos h2] at ht
    have hdg : (Dg (gs ++ [g]) n marked).getD t 0 = g.lineDegree (Dg gs n marked) := by
      rw [Dg_snoc, getD_snoc, if_neg (by omega), if_pos (by omega)]
    have hwg : ∀ T, (W (gs ++ [g]) (rst marked T x)).getD t false =
        g.op.eval (g.inputs.map fun i => (W gs (rst marked T x)).getD i false) := by
      intro T
      rw [W_snoc, getD_snoc, hlenW, if_neg h1, if_pos h2]
    simp only [hdg, hwg]
    -- monotonicity of the prefix wires in T
    have hmonoT : ∀ T U, T ⊆ U → ∀ i, (W gs (rst marked T x)).getD i false = true →
        (W gs (rst marked U x)).getD i false = true := by
      intro T U hTU i hi
      exact W_mono gs hm' _ _ (by simp [rst_length]) (rst_mono marked hTU x) i hi
    rcases hm g (by simp) with hg | hg
    · -- AND
      rw [hg] at ht ⊢
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at ht
      have key : ∀ l : List ℕ, (∀ i ∈ l, (W gs x).getD i false = true) →
          ∃ U ⊆ lines marked x, U.card ≤ (l.map fun i => (Dg gs n marked).getD i 0).sum ∧
            ∀ i ∈ l, (W gs (rst marked U x)).getD i false = true := by
        intro l
        induction l with
        | nil => intro _; exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
        | cons a l ihl =>
          intro hl
          obtain ⟨T, hTL, hTc, hTv⟩ := ih a (hl a (by simp))
          obtain ⟨U, hUL, hUc, hUv⟩ := ihl (fun i hi => hl i (by simp [hi]))
          refine ⟨T ∪ U, Finset.union_subset hTL hUL, ?_, ?_⟩
          · simp only [List.map_cons, List.sum_cons]
            exact le_trans (Finset.card_union_le _ _) (by omega)
          · intro i hi
            rcases List.mem_cons.1 hi with hi | hi
            · subst hi; exact hmonoT T _ Finset.subset_union_left _ hTv
            · exact hmonoT U _ Finset.subset_union_right _ (hUv i hi)
      obtain ⟨U, hUL, hUc, hUv⟩ := key g.inputs ht
      refine ⟨U, hUL, ?_, ?_⟩
      · simp only [Gate.lineDegree, hg, if_true]; exact hUc
      · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
        exact hUv
    · -- OR
      rw [hg] at ht ⊢
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at ht
      obtain ⟨i, hi, hv⟩ := ht
      obtain ⟨T, hTL, hTc, hTv⟩ := ih i hv
      refine ⟨T, hTL, ?_, ?_⟩
      · simp only [Gate.lineDegree, hg, reduceCtorEq, if_false]
        exact le_trans hTc (le_foldr_max (List.mem_map.2 ⟨i, hi, rfl⟩))
      · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        exact ⟨i, hi, hTv⟩

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (k : ℕ) :
    (List.ofFn f).getD k false = if h : k < n then f ⟨k, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : k < n <;> simp [h]

/-- The test lemma for line-degree (the statement of L-meta-629). -/
theorem main : ∀ (n D : ℕ) (marked : Finset ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ i j : Fin n, G.Adj i j → (i.val ∈ marked ↔ j.val ∉ marked)) →
    PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C →
    PEqualNP.CircuitLowerBounds.HasLineDegree n marked C D →
    (∀ i j : Fin n, G.Adj i j → C.eval (List.ofFn fun k => decide (k = i ∨ k = j)) = true) →
    (∀ S : Finset (Fin n), (∀ j ∈ S, j.val ∈ marked) → S.card ≤ D →
      C.eval (List.ofFn fun k => decide (k ∈ S ∨ (k.val ∉ marked ∧ ∀ j ∈ S, ¬ G.Adj k j)))
        = false) →
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
  intro n D marked G _ C _ hmono hdeg hedge htest x
  have hW : ∀ y, C.eval y = (W C.gates y).getD C.output false := fun y => rfl
  have hD : C.lineDeg n marked = (Dg C.gates n marked).getD C.output 0 := rfl
  have hmono' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hmono
  constructor
  · intro hx
    by_contra hne
    push_neg at hne
    rw [hW] at hx
    obtain ⟨T, hTL, hTc, hTv⟩ := inv marked C.gates hmono' n (List.ofFn x) (by simp) C.output hx
    have hTD : T.card ≤ D := le_trans hTc (by rw [← hD]; exact hdeg)
    have hTmem : ∀ i ∈ T, i < n ∧ i ∈ marked ∧ (List.ofFn x).getD i false = true := by
      intro i hi
      have := hTL hi
      simp only [lines, Finset.mem_filter, Finset.mem_range, List.length_ofFn] at this
      exact this
    let S : Finset (Fin n) := Finset.univ.filter fun k => k.val ∈ T
    have hS1 : ∀ j ∈ S, j.val ∈ marked := by
      intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact (hTmem _ hj).2.1
    have hScard : S.card ≤ D := by
      refine le_trans ?_ hTD
      refine Finset.card_le_card_of_injOn (fun k => k.val) ?_ ?_
      · intro k hk
        simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk
        exact hk
      · intro a _ b _ hab; exact Fin.ext hab
    have hfalse := htest S hS1 hScard
    rw [hW] at hfalse
    have hle : Le (rst marked T (List.ofFn x))
        (List.ofFn fun k => decide (k ∈ S ∨ (k.val ∉ marked ∧ ∀ j ∈ S, ¬ G.Adj k j))) := by
      intro k hk
      rw [rst_getD] at hk
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk
      obtain ⟨hxk, hk2⟩ := hk
      rw [ofFn_getD] at hxk ⊢
      by_cases hkn : k < n
      swap
      · rw [dif_neg hkn] at hxk; exact absurd hxk (by simp)
      rw [dif_pos hkn] at hxk ⊢
      simp only [decide_eq_true_eq]
      by_cases hkT : k ∈ T
      · left; simp [S, hkT]
      · right
        have hkm : k ∉ marked := by
          rcases hk2 with h | h
          · exact h
          · exact absurd h hkT
        refine ⟨hkm, ?_⟩
        intro j hj hadj
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hxj := (hTmem _ hj).2.2
        rw [ofFn_getD, dif_pos j.isLt] at hxj
        exact hne ⟨k, hkn⟩ j hadj hxk hxj
    have := W_mono C.gates hmono' _ _ (by simp [rst_length]) hle C.output hTv
    rw [hfalse] at this
    exact absurd this (by simp)
  · rintro ⟨i, j, hij, hi, hj⟩
    have h := hedge i j hij
    rw [hW] at h ⊢
    refine W_mono C.gates hmono' _ _ (by simp) ?_ C.output h
    intro k hk
    rw [ofFn_getD] at hk ⊢
    by_cases hkn : k < n
    · rw [dif_pos hkn] at hk ⊢
      simp only [decide_eq_true_eq] at hk
      rcases hk with hk | hk
      · rw [hk]; exact hi
      · rw [hk]; exact hj
    · rw [dif_neg hkn] at hk; exact absurd hk (by simp)

end PEqualNP.MetaComplexity.LineDegTest
