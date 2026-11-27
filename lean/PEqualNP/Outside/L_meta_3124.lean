import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3124_aux

open PEqualNP.CircuitLowerBounds

def pf (x : Fin 9 → Bool) : Bool := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def nb (j : Fin 9) : Fin 9 :=
  if j = 0 then 1 else if j = 1 then 0 else if j = 2 then 1 else if j = 3 then 2
  else if j = 4 then 3 else if j = 5 then 0 else if j = 6 then 1 else if j = 7 then 2 else 3

def Dep (S : Finset (Fin 9)) (v : (Fin 9 → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → v x = v y

def X8 (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def W (x1 : List ℕ) (x : Fin 9 → Bool) : List Bool :=
  X8 x ++ [GateOp.or.eval (List.map (fun i => (X8 x).getD i false) x1)]

theorem core (out : (Fin 9 → Bool) → Bool) (S : Finset (Fin 9)) (hS : S.card ≤ 4)
    (h : Dep S out) : ∃ x, out x ≠ pf x := by
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra hc
    push_neg at hc
    have h2 : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hc
    rw [h2] at hS
    simp at hS
  by_contra hc
  push_neg at hc
  have h1 := h (fun i => decide (i = nb j)) (fun i => decide (i = nb j ∨ i = j)) (by
    intro i hi
    have h3 : i ≠ j := by
      rintro rfl
      exact hj hi
    simp [h3])
  rw [hc, hc] at h1
  clear hj hc h hS
  revert j
  decide

theorem getD_snoc (A : List Bool) (v : Bool) (k : ℕ) :
    (A ++ [v]).getD k false
      = if k < A.length then A.getD k false else if k = A.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem x8len (x : Fin 9 → Bool) : (X8 x).length = 10 := by simp [X8]

theorem wlen (x1 : List ℕ) (x : Fin 9 → Bool) : (W x1 x).length = 11 := by simp [W, x8len]

theorem dep8 (k : ℕ) : ∃ S : Finset (Fin 9), S.card ≤ 1 ∧ Dep S (fun x => (X8 x).getD k false) := by
  by_cases hk : k < 10
  · refine ⟨{if h : k < 9 then ⟨k, h⟩ else 0}, by simp, ?_⟩
    intro x y h
    have h2 := h _ (Finset.mem_singleton_self _)
    interval_cases k <;> simp_all [X8, List.ofFn_succ]
  · refine ⟨∅, by simp, ?_⟩
    intro x y _
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [x8len]; omega), List.getElem?_eq_none (by rw [x8len]; omega)]

theorem depList (c : ℕ) (w : ℕ → (Fin 9 → Bool) → Bool)
    (hw : ∀ k, ∃ S : Finset (Fin 9), S.card ≤ c ∧ Dep S (w k)) (l : List ℕ) (hl : l.length ≤ 2) :
    ∃ S : Finset (Fin 9), S.card ≤ 2 * c ∧
      ∀ x y, (∀ i ∈ S, x i = y i) → l.map (fun k => w k x) = l.map (fun k => w k y) := by
  match l, hl with
  | [], _ => exact ⟨∅, by simp, by simp⟩
  | [a], _ =>
    obtain ⟨S, hS, hd⟩ := hw a
    exact ⟨S, by omega, fun x y h => by simp [hd x y h]⟩
  | [a, b], _ =>
    obtain ⟨S, hS, hd⟩ := hw a
    obtain ⟨T, hT, he⟩ := hw b
    refine ⟨S ∪ T, ?_, fun x y h => ?_⟩
    · have := Finset.card_union_le S T
      omega
    · have h1 := hd x y (fun i hi => h i (Finset.mem_union_left _ hi))
      have h2 := he x y (fun i hi => h i (Finset.mem_union_right _ hi))
      simp [h1, h2]
  | _ :: _ :: _ :: _, h => simp at h

theorem depW (x1 : List ℕ) (h1 : x1.length ≤ 2) (k : ℕ) :
    ∃ S : Finset (Fin 9), S.card ≤ 2 ∧ Dep S (fun x => (W x1 x).getD k false) := by
  by_cases hk : k < 10
  · obtain ⟨S, hS, hd⟩ := dep8 k
    refine ⟨S, by omega, fun x y h => ?_⟩
    have := hd x y h
    simp only [W, getD_snoc, x8len, if_pos hk]
    exact this
  · by_cases hk2 : k = 10
    · obtain ⟨S, hS, hd⟩ := depList 1 (fun k x => (X8 x).getD k false) dep8 x1 h1
      refine ⟨S, by omega, fun x y h => ?_⟩
      have := hd x y h
      simp only [W, getD_snoc, x8len, if_neg hk, if_pos hk2]
      exact congrArg GateOp.or.eval this
    · refine ⟨∅, by simp, fun x y _ => ?_⟩
      simp only [W, getD_snoc, x8len, if_neg hk, if_neg hk2]

theorem depC (x1 : List ℕ) (h1 : x1.length ≤ 2) (x3 : Circuit)
    (hf : ∀ g ∈ x3.gates, g.inputs.length ≤ 2)
    (h3 : ¬∃ x6 : Gate, x3.gates[1]? = some x6) :
    ∃ S : Finset (Fin 9), S.card ≤ 4 ∧ Dep S (fun x => x3.eval (W x1 x)) := by
  obtain ⟨gates, out⟩ := x3
  match gates, hf, h3 with
  | [], _, _ =>
    obtain ⟨S, hS, hd⟩ := depW x1 h1 out
    exact ⟨S, by omega, hd⟩
  | [g], hf, _ =>
    have hg : g.inputs.length ≤ 2 := hf g (by simp)
    by_cases hk : out < 11
    · obtain ⟨S, hS, hd⟩ := depW x1 h1 out
      refine ⟨S, by omega, fun x y h => ?_⟩
      have := hd x y h
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, getD_snoc, wlen,
        if_pos hk]
      exact this
    · by_cases hk2 : out = 11
      · obtain ⟨S, hS, hd⟩ := depList 2 (fun k x => (W x1 x).getD k false) (depW x1 h1) g.inputs hg
        refine ⟨S, by omega, fun x y h => ?_⟩
        have := hd x y h
        simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, getD_snoc, wlen,
          if_neg hk, if_pos hk2]
        exact congrArg g.op.eval this
      · refine ⟨∅, by simp, fun x y _ => ?_⟩
        simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, getD_snoc, wlen,
          if_neg hk, if_neg hk2]
  | _ :: _ :: _, _, h => exact absurd h (by simp)

end PEqualNP.Outside.L_meta_3124_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3124_aux in
theorem PEqualNP.Outside.L_meta_3124 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 h1 x3 hf _ h3
  obtain ⟨S, hS, hd⟩ := depC x1 h1 x3 (fun g hg => (hf g hg).2) h3
  exact core (fun x => x3.eval (W x1 x)) S hS hd
