import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6204

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




theorem ren2 {α : Type} (z : α) (ρ : ℕ → ℕ) (F : Gate → List α → α) (r : Gate → Gate)
    (hF : ∀ g d d', (∀ k, d'.getD (ρ k) z = d.getD k z) → F (r g) d' = F g d) :
    ∀ (gs : List Gate) (d d' : List α), (∀ k, d.length ≤ k → k < d.length + gs.length → ρ k = d'.length + (k - d.length)) →
      (∀ k, k < d.length → ρ k < d'.length) → (∀ k, d.length + gs.length ≤ k → d'.length + gs.length ≤ ρ k) → (∀ k, k < d.length → d'.getD (ρ k) z = d.getD k z) →
      ∀ k, ((gs.map r).foldl (fun d g => d ++ [F g d]) d').getD (ρ k) z = (gs.foldl (fun d g => d ++ [F g d]) d).getD k z := by
  intro gs
  induction gs with
  | nil =>
    intro d d' h1 h2 h3 h4 k
    by_cases hk : k < d.length
    · exact h4 k hk
    · simp only [List.map_nil, List.foldl_nil, List.length_nil, Nat.add_zero] at h3 ⊢
      rw [List.getD_eq_default _ _ (h3 k (by omega)), List.getD_eq_default _ _ (by omega)]
  | cons g gs ih =>
    intro d d' h1 h2 h3 h4
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    simp only [List.length_cons] at h1 h3
    have all : ∀ k, d'.getD (ρ k) z = d.getD k z := by
      intro k
      by_cases hk : k < d.length
      · exact h4 k hk
      · rw [List.getD_eq_default d _ (by omega)]
        refine List.getD_eq_default _ _ ?_
        by_cases hk2 : k < d.length + (gs.length + 1)
        · rw [h1 k (by omega) hk2]; omega
        · have := h3 k (by omega); omega
    have e0 : ρ d.length = d'.length := by have := h1 d.length le_rfl (by omega); omega
    refine ih _ _ ?_ ?_ ?_ ?_
    · intro k hk1 hk2
      simp only [List.length_append, List.length_singleton] at hk1 hk2 ⊢
      rw [h1 k (by omega) (by omega)]; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      rcases Nat.lt_or_ge k d.length with h | h
      · have := h2 k h; omega
      · have : k = d.length := by omega
        rw [this, e0]; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk ⊢
      have := h3 k (by omega); omega
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      rw [hF g d d' all]
      rcases Nat.lt_or_ge k d.length with h | h
      · have := h4 k h
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this ⊢
        rw [List.getElem?_append_left (h2 k h), List.getElem?_append_left h]; exact this
      · have : k = d.length := by omega
        rw [this, e0]
        simp [List.getD_eq_getElem?_getD]

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6204

theorem PEqualNP.Outside.L_meta_6204 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (13 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → x1.output < (13 : ℕ) + x1.size → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x5 ∧ (∀ x6 ∈ x5.gates, x6.inputs.Nodup) ∧ (2 : ℕ) ≤ x5.size ∧ x5.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x5.eval (List.ofFn x6) = (x6 (0 : Fin (14 : ℕ)) && (x6 (8 : Fin (14 : ℕ)) || x6 (10 : Fin (14 : ℕ)) || x6 (7 : Fin (14 : ℕ))) || x6 (1 : Fin (14 : ℕ)) && (x6 (9 : Fin (14 : ℕ)) || x6 (13 : Fin (14 : ℕ)) || x6 (7 : Fin (14 : ℕ))) || x6 (3 : Fin (14 : ℕ)) && (x6 (11 : Fin (14 : ℕ)) || x6 (12 : Fin (14 : ℕ)) || x6 (7 : Fin (14 : ℕ))) || x1.eval [x6 (2 : Fin (14 : ℕ)), x6 (4 : Fin (14 : ℕ)), x6 (5 : Fin (14 : ℕ)), x6 (6 : Fin (14 : ℕ)), x6 (8 : Fin (14 : ℕ)), x6 (9 : Fin (14 : ℕ)), x6 (10 : Fin (14 : ℕ)), x6 (11 : Fin (14 : ℕ)), x6 (12 : Fin (14 : ℕ)), x6 (13 : Fin (14 : ℕ)), x6 (8 : Fin (14 : ℕ)) || x6 (10 : Fin (14 : ℕ)), x6 (9 : Fin (14 : ℕ)) || x6 (13 : Fin (14 : ℕ)), x6 (11 : Fin (14 : ℕ)) || x6 (12 : Fin (14 : ℕ))]) := by
  intro C hC hnd ho
  let ρ : ℕ → ℕ := fun i => [2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16].getD i (i + 4)
  have ρ1 : ∀ i, i < 13 → ρ i < 17 := by intro i hi; interval_cases i <;> decide
  have ρ2 : ∀ i, 13 ≤ i → ρ i = i + 4 := by
    intro i hi
    exact List.getD_eq_default _ _ (by simp; omega)
  have ρi : Function.Injective ρ := by
    intro a b h
    by_cases ha : a < 13 <;> by_cases hb : b < 13
    · revert h; interval_cases a <;> interval_cases b <;> first | (intro _; rfl) | (intro h; exact absurd h (by decide))
    · have h1 := ρ1 a ha; rw [h, ρ2 b (by omega)] at h1; omega
    · have h1 := ρ1 b hb; rw [← h, ρ2 a (by omega)] at h1; omega
    · rw [ρ2 a (by omega), ρ2 b (by omega)] at h; omega
  let O := PEqualNP.CircuitLowerBounds.GateOp.or
  let A := PEqualNP.CircuitLowerBounds.GateOp.and
  let pre : List PEqualNP.CircuitLowerBounds.Gate := [⟨O, [8, 10]⟩, ⟨O, [9, 13]⟩, ⟨O, [11, 12]⟩]
  let mid : List PEqualNP.CircuitLowerBounds.Gate := C.gates.map fun g => ⟨g.op, g.inputs.map ρ⟩
  let N := 17 + C.gates.length
  let post : List PEqualNP.CircuitLowerBounds.Gate := [⟨O, [14, 7]⟩, ⟨A, [0, N]⟩, ⟨O, [15, 7]⟩, ⟨A, [1, N + 2]⟩, ⟨O, [16, 7]⟩, ⟨A, [3, N + 4]⟩, ⟨O, [N + 1, N + 3]⟩, ⟨O, [N + 6, N + 5]⟩, ⟨O, [N + 7, ρ C.output]⟩]
  have hmid : mid.length = C.gates.length := by simp [mid]
  have hro0 : ρ C.output < N := by
    by_cases h : C.output < 13
    · have := ρ1 _ h; simp only [N]; omega
    · rw [ρ2 _ (by omega)]
      have : C.size = C.gates.length := rfl
      simp only [N]; omega
  have postgood : ∀ (q : ℕ) (hq : q < post.length), (post[q].op = A ∨ post[q].op = O) ∧ post[q].inputs.length = 2 ∧ post[q].inputs.Nodup ∧ ∀ i ∈ post[q].inputs, i < 17 + C.gates.length + q := by
    intro q hq
    have hq9 : q < 9 := hq
    have hN : N = 17 + C.gates.length := rfl
    interval_cases q <;> simp [post, O, A] <;> omega
  have good : ∀ (j : ℕ) (hj : j < (pre ++ (mid ++ post)).length), ((pre ++ (mid ++ post))[j].op = A ∨ (pre ++ (mid ++ post))[j].op = O) ∧
      (pre ++ (mid ++ post))[j].inputs.length = 2 ∧ (pre ++ (mid ++ post))[j].inputs.Nodup ∧ ∀ i ∈ (pre ++ (mid ++ post))[j].inputs, i < 14 + j := by
    intro j hj
    have hro : ρ C.output < N := by
      by_cases h : C.output < 13
      · have := ρ1 _ h; simp only [N]; omega
      · rw [ρ2 _ (by omega)]
        have : C.size = C.gates.length := rfl
        simp only [N]; omega
    rcases Nat.lt_or_ge j 3 with h | h
    · rw [List.getElem_append_left (by simpa [pre] using h)]
      interval_cases j <;> simp [pre, O, A]
    · rw [List.getElem_append_right (by simpa [pre] using h)]
      have hp : pre.length = 3 := rfl
      rcases Nat.lt_or_ge (j - 3) C.gates.length with h2 | h2
      · rw [List.getElem_append_left (by rw [hp, hmid]; exact h2)]
        simp only [mid, List.getElem_map, hp]
        have hg := List.getElem_mem h2
        have h5 := hC.2.1 (j - 3) h2
        have e : PEqualNP.MetaComplexity.NestedCover.gateAt C (j - 3) = C.gates[j - 3] := List.getD_eq_getElem _ _ h2
        rw [e] at h5
        refine ⟨hC.1 _ hg, by rw [List.length_map]; exact hC.2.2 _ hg, (hnd _ hg).map ρi, ?_⟩
        intro i hi
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
        have := h5 k hk
        by_cases hk13 : k < 13
        · have := ρ1 k hk13; omega
        · rw [ρ2 k (by omega)]; omega
      · rw [List.getElem_append_right (by rw [hp, hmid]; exact h2)]
        have hpl : post.length = 9 := rfl
        have hj' : j - 3 - C.gates.length < 9 := by
          simp only [List.length_append, hp, hmid, hpl] at hj; omega
        have key := postgood (j - 3 - C.gates.length) hj'
        simp only [hp, hmid]
        refine ⟨key.1, key.2.1, key.2.2.1, fun i hi => ?_⟩
        have := key.2.2.2 i hi
        omega
  refine ⟨⟨pre ++ (mid ++ post), 14 + (3 + C.gates.length + 8)⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact (good j hj).1
  · intro j hj i hi
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨pre ++ (mid ++ post), 14 + (3 + C.gates.length + 8)⟩ j = (pre ++ (mid ++ post))[j] := List.getD_eq_getElem _ _ hj
    rw [e] at hi
    exact (good j hj).2.2.2 i hi
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact (good j hj).2.1
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    exact (good j hj).2.2.1
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, pre, post, List.length_append, List.length_cons]; omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, pre, post, mid, List.length_append, List.length_cons, List.length_nil, List.length_map]; omega
  · intro x
    let X0 : List Bool := List.ofFn x
    let X1 : List Bool := X0 ++ [x 8 || x 10] ++ [x 9 || x 13] ++ [x 11 || x 12]
    have hx0 : X0.length = 14 := by simp [X0]
    have d0 : ∀ k : Fin 14, X0.getD k false = x k := by
      intro k
      simp only [X0]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos k.isLt]
      rfl
    have g0 : ∀ i : ℕ, (h : i < 14) → X0.getD i false = x ⟨i, h⟩ := fun i h => d0 ⟨i, h⟩
    have hpre : PEqualNP.Outside.L_meta_6204.run pre X0 = X1 := by
      have s1 : ∀ i b, i < 14 → (X0 ++ [b]).getD i false = X0.getD i false := fun i b h => PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by omega)
      have s2 : ∀ i b c, i < 14 → (X0 ++ [b] ++ [c]).getD i false = X0.getD i false := fun i b c h => by
        rw [PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by simp [hx0]; omega), s1 i b h]
      have e : PEqualNP.Outside.L_meta_6204.run pre X0 = X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)] ++ [(X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)]).getD 9 false || ((X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)]).getD 13 false || false)] ++
          [(X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)] ++ [(X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)]).getD 9 false || ((X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)]).getD 13 false || false)]).getD 11 false ||
            ((X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)] ++ [(X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)]).getD 9 false || ((X0 ++ [X0.getD 8 false || (X0.getD 10 false || false)]).getD 13 false || false)]).getD 12 false || false)] := rfl
      rw [e, s2 11 _ _ (by omega), s2 12 _ _ (by omega), s1 9 _ (by omega), s1 13 _ (by omega)]
      rw [g0 8 (by omega), g0 10 (by omega), g0 9 (by omega), g0 13 (by omega), g0 11 (by omega), g0 12 (by omega)]
      simp only [Bool.or_false]
      rfl
    have hX1 : X1.length = 17 := by simp [X1, hx0]
    have v1 : ∀ i : ℕ, (h : i < 14) → X1.getD i false = x ⟨i, h⟩ := by
      intro i h
      simp only [X1]
      rw [PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by simp [hx0]; omega), PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by simp [hx0]; omega), PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by omega), g0 i h]
    have v14 : X1.getD 14 false = (x 8 || x 10) := by
      simp only [X1]
      rw [PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by simp [hx0]), PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by simp [hx0])]
      have := PEqualNP.Outside.L_meta_6204.getD_at X0 (x 8 || x 10)
      rwa [hx0] at this
    have v15 : X1.getD 15 false = (x 9 || x 13) := by
      simp only [X1]
      rw [PEqualNP.Outside.L_meta_6204.getD_lt _ _ _ (by simp [hx0])]
      have := PEqualNP.Outside.L_meta_6204.getD_at (X0 ++ [x 8 || x 10]) (x 9 || x 13)
      simpa [hx0] using this
    have v16 : X1.getD 16 false = (x 11 || x 12) := by
      simp only [X1]
      have := PEqualNP.Outside.L_meta_6204.getD_at (X0 ++ [x 8 || x 10] ++ [x 9 || x 13]) (x 11 || x 12)
      simpa [hx0] using this
    let Y : List Bool := [x 2, x 4, x 5, x 6, x 8, x 9, x 10, x 11, x 12, x 13, x 8 || x 10, x 9 || x 13, x 11 || x 12]
    have hren := PEqualNP.Outside.L_meta_6204.ren2 false ρ (fun g d => g.op.eval (g.inputs.map fun i => d.getD i false)) (fun g => ⟨g.op, g.inputs.map ρ⟩) (by
      intro g d d' h
      simp only [List.map_map]
      congr 1
      exact List.map_congr_left fun i _ => h i) C.gates Y X1 (by
      intro k hk _
      have hy : Y.length = 13 := rfl
      rw [hX1, hy, ρ2 k (by omega)]; omega) (by
      intro k hk
      rw [hX1]; exact ρ1 k hk) (by
      intro k hk
      have hy : Y.length = 13 := rfl
      rw [hX1, ρ2 k (by omega)]; omega) (by
      intro k hk
      have hk' : k < 13 := hk
      interval_cases k
      · exact v1 2 (by omega)
      · exact v1 4 (by omega)
      · exact v1 5 (by omega)
      · exact v1 6 (by omega)
      · exact v1 8 (by omega)
      · exact v1 9 (by omega)
      · exact v1 10 (by omega)
      · exact v1 11 (by omega)
      · exact v1 12 (by omega)
      · exact v1 13 (by omega)
      · exact v14
      · exact v15
      · exact v16)
    let Z : List Bool := PEqualNP.Outside.L_meta_6204.run mid X1
    have hZ : Z.length = N := by simp only [Z]; rw [PEqualNP.Outside.L_meta_6204.run_length, hX1, hmid]
    have z1 : ∀ i, i < 17 → Z.getD i false = X1.getD i false := fun i hi => PEqualNP.Outside.L_meta_6204.run_input _ _ _ (by omega)
    have zo : Z.getD (ρ C.output) false = C.eval Y := hren C.output
    have hrun : PEqualNP.Outside.L_meta_6204.run (pre ++ (mid ++ post)) X0 = PEqualNP.Outside.L_meta_6204.run post Z := by
      simp only [Z, ← hpre]
      simp only [PEqualNP.Outside.L_meta_6204.run, List.foldl_append]
    have step : ∀ (W : List Bool) (i : ℕ) (b : Bool), i < W.length → (W ++ [b]).getD i false = W.getD i false := fun W i b h => PEqualNP.Outside.L_meta_6204.getD_lt W b i h
    have hro : ρ C.output < N := by
      by_cases h : C.output < 13
      · have := ρ1 _ h; simp only [N]; omega
      · rw [ρ2 _ (by omega)]
        have : C.size = C.gates.length := rfl
        simp only [N]; omega
    change (PEqualNP.Outside.L_meta_6204.run (pre ++ (mid ++ post)) X0).getD (14 + (3 + C.gates.length + 8)) false = _
    rw [hrun]
    -- the nine last gates
    let w0 := Z.getD 14 false || Z.getD 7 false
    let w1 := Z.getD 0 false && w0
    let w2 := Z.getD 15 false || Z.getD 7 false
    let w3 := Z.getD 1 false && w2
    let w4 := Z.getD 16 false || Z.getD 7 false
    let w5 := Z.getD 3 false && w4
    let w6 := w1 || w3
    let w7 := w6 || w5
    let w8 := w7 || Z.getD (ρ C.output) false
    have hpost : PEqualNP.Outside.L_meta_6204.run post Z = Z ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8] := by
      have ap : ∀ (l : List Bool) (i : ℕ), i < N → (Z ++ l).getD i false = Z.getD i false := by
        intro l i hi
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < Z.length by omega)]
      have aq : ∀ (l : List Bool) (i : ℕ), (Z ++ l).getD (N + i) false = l.getD i false := by
        intro l i
        rw [← hZ]
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      have aq0 : ∀ (l : List Bool), (Z ++ l).getD N false = l.getD 0 false := fun l => aq l 0
      have hN : 17 ≤ N := by simp only [N]; omega
      have z14 := fun l => ap l 14 (by omega)
      have z7 := fun l => ap l 7 (by omega)
      have z0 := fun l => ap l 0 (by omega)
      have z15 := fun l => ap l 15 (by omega)
      have z11 := fun l => ap l 1 (by omega)
      have z16 := fun l => ap l 16 (by omega)
      have z3 := fun l => ap l 3 (by omega)
      have zr := fun l => ap l (ρ C.output) hro
      simp only [post, PEqualNP.Outside.L_meta_6204.run, List.foldl_cons, List.foldl_nil, O, A, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append, List.nil_append,
        z14, z7, z0, z15, z11, z16, z3, zr, aq, aq0, List.getD_cons_zero, List.getD_cons_succ]
      rfl
    rw [hpost]
    have e1 : (Z ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8]).getD (14 + (3 + C.gates.length + 8)) false = w8 := by
      have : 14 + (3 + C.gates.length + 8) = Z.length + 8 := by rw [hZ]; simp only [N]; omega
      rw [this]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    rw [e1]
    simp only [w8, w7, w6, w5, w4, w3, w2, w1, w0, zo]
    rw [z1 14 (by omega), z1 7 (by omega), z1 0 (by omega), z1 15 (by omega), z1 1 (by omega), z1 16 (by omega), z1 3 (by omega), v14, v15, v16, v1 7 (by omega), v1 0 (by omega), v1 1 (by omega), v1 3 (by omega)]
    rfl
