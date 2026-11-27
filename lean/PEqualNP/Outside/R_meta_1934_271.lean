import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1934_271
    (group0 : ∀ i : Fin 11, i ∈ ([0, 1, 3] : List (Fin 11)) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          ∃ x : Fin 9 → Bool,
            C.eval ((List.ofFn x ++ [x 0 && x 2]) ++
              [!(List.ofFn x ++ [x 0 && x 2]).getD i.val false]) ≠
              ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (group1 : ∀ i : Fin 11, i ∈ ([4, 6, 8] : List (Fin 11)) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          ∃ x : Fin 9 → Bool,
            C.eval ((List.ofFn x ++ [x 0 && x 2]) ++
              [!(List.ofFn x ++ [x 0 && x 2]).getD i.val false]) ≠
              ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (group2 : ∀ i : Fin 11, i ∈ ([9, 10] : List (Fin 11)) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          ∃ x : Fin 9 → Bool,
            C.eval ((List.ofFn x ++ [x 0 && x 2]) ++
              [!(List.ofFn x ++ [x 0 && x 2]).getD i.val false]) ≠
              ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let seed (x : Fin 9 → Bool) : List Bool :=
    List.ofFn x ++ [x 0 && x 2]

  let canonical (xs : List ℕ) : Fin 11 :=
    ⟨min (xs.headD 10) 10, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

  have seed_length (x : Fin 9 → Bool) : (seed x).length = 10 := by
    simp [seed]

  have getD_clamp (x : Fin 9 → Bool) (i : ℕ) :
      (seed x).getD i false = (seed x).getD (min i 10) false := by
    by_cases h : i < 10
    · rw [Nat.min_eq_left (by omega : i ≤ 10)]
    · rw [List.getD_eq_default _ _ (by simpa [seed_length] using h)]
      rw [Nat.min_eq_right (by omega : 10 ≤ i)]
      exact (List.getD_eq_default _ _ (by simp [seed_length])).symm

  have not_normalize (xs : List ℕ) (x : Fin 9 → Bool) :
      PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (xs.map fun i => (seed x).getD i false) =
      !(seed x).getD (canonical xs).val false := by
    cases xs with
    | nil =>
      change true = Bool.not ((seed x).getD 10 false)
      rw [List.getD_eq_default _ _ (by simp [seed_length])]
      rfl
    | cons i rest =>
      change Bool.not ((seed x).getD i false) =
        Bool.not ((seed x).getD (min i 10) false)
      rw [getD_clamp]

  let target (x : Fin 9 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

  let completionFails (xs : List ℕ) : Prop :=
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        C.eval (seed x ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (xs.map fun i => (seed x).getD i false)]) ≠ target x

  have finite_reduction :
      (∀ xs : List ℕ, xs.length ≤ 2 → completionFails xs) ↔
      (∀ i : Fin 11, completionFails [i.val]) := by
    constructor
    · intro h i
      exact h [i.val] (by simp)
    · intro h xs _ C hf hs
      obtain ⟨x, hx⟩ := h (canonical xs) C hf hs
      refine ⟨x, ?_⟩
      have hn : PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (([(canonical xs).val] : List ℕ).map fun i => (seed x).getD i false) =
          PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (xs.map fun i => (seed x).getD i false) := by
        exact (not_normalize xs x).symm
      simpa only [hn] using hx

  let swapSeed : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]

  have swapSeed_involution : ∀ i : Fin 9, swapSeed (swapSeed i) = i := by
    decide +kernel

  have target_swapSeed (x : Fin 9 → Bool) :
      target (fun i => x (swapSeed i)) = target x := by
    dsimp [target, swapSeed]
    ac_rfl

  let renameGate (ρ : ℕ → ℕ) (g : Gate) : Gate :=
    { op := g.op, inputs := g.inputs.map ρ }

  let renameCircuit (ρ : ℕ → ℕ) (C : Circuit) : Circuit :=
    { gates := C.gates.map (renameGate ρ), output := ρ C.output }

  let wireRel (ρ : ℕ → ℕ) (w v : List Bool) : Prop :=
    ∀ i, v.getD (ρ i) false = w.getD i false

  have wireRel_append (ρ : ℕ → ℕ) (n : ℕ)
      (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
      (w v : List Bool) (hlen : w.length = v.length) (hn : n ≤ w.length)
      (hrel : wireRel ρ w v) (b : Bool) : wireRel ρ (w ++ [b]) (v ++ [b]) := by
    intro i
    by_cases hi : i < w.length
    · have hri : ρ i < v.length := by
        by_cases hin : i < n
        · have := hlt i hin
          omega
        · rw [hfix i (by omega)]
          omega
      rw [List.getD_append _ _ _ _ hri, List.getD_append _ _ _ _ hi]
      exact hrel i
    · have hin : n ≤ i := by omega
      rw [hfix i hin]
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen]

  have wires_rename (ρ : ℕ → ℕ) (n : ℕ)
      (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
      (gs : List Gate) (w v : List Bool) (hlen : w.length = v.length)
      (hn : n ≤ w.length) (hrel : wireRel ρ w v) :
      wireRel ρ
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        ((gs.map (renameGate ρ)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
    induction gs generalizing w v with
    | nil => exact hrel
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons]
      have hval : (renameGate ρ g).op.eval
          ((renameGate ρ g).inputs.map fun i => v.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [renameGate, List.map_map]
        congr 2
        exact funext hrel
      rw [hval]
      apply ih
      · simp [hlen]
      · simp only [List.length_append, List.length_singleton]
        omega
      · exact wireRel_append ρ n hfix hlt w v hlen hn hrel _

  have eval_rename (ρ : ℕ → ℕ) (n : ℕ)
      (hfix : ∀ i, n ≤ i → ρ i = i) (hlt : ∀ i, i < n → ρ i < n)
      (C : Circuit) (w v : List Bool) (hlen : w.length = v.length)
      (hn : n ≤ w.length) (hrel : wireRel ρ w v) :
      (renameCircuit ρ C).eval v = C.eval w := by
    exact wires_rename ρ n hfix hlt C.gates w v hlen hn hrel C.output

  have size_rename (ρ : ℕ → ℕ) (C : Circuit) :
      (renameCircuit ρ C).size = C.size := by
    change (C.gates.map (renameGate ρ)).length = C.gates.length
    simp only [List.length_map]

  have fanInTwo_rename (ρ : ℕ → ℕ) (C : Circuit)
      (hf : PEqualNP.MetaComplexity.FanInTwo C) :
      PEqualNP.MetaComplexity.FanInTwo (renameCircuit ρ C) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen⟩ := hf g' hg'
    exact ⟨hop, by simpa [renameGate] using hlen⟩

  let wireSwap (i : ℕ) : ℕ :=
    if h : i < 9 then (swapSeed ⟨i, h⟩).val else i

  have wireSwap_fix (i : ℕ) (hi : 9 ≤ i) : wireSwap i = i := by
    simp [wireSwap, Nat.not_lt.mpr hi]

  have wireSwap_lt (i : ℕ) (hi : i < 9) : wireSwap i < 9 := by
    simpa [wireSwap, hi] using (swapSeed ⟨i, hi⟩).isLt

  have seed_swap_rel (x : Fin 9 → Bool) :
      wireRel wireSwap (seed x) (seed (fun i => x (swapSeed i))) := by
    intro i
    by_cases hi : i < 10
    · interval_cases i <;>
        simp [seed, wireSwap, swapSeed, List.ofFn_succ, Bool.and_comm]
    · rw [wireSwap_fix i (by omega)]
      rw [List.getD_eq_default _ _ (by simp [seed_length]; omega),
        List.getD_eq_default _ _ (by simp [seed_length]; omega)]

  let completionInput (x : Fin 9 → Bool) (i : ℕ) : List Bool :=
    seed x ++ [!(seed x).getD i false]

  have completionInput_swap_rel (x : Fin 9 → Bool) (i : ℕ) :
      wireRel wireSwap (completionInput x i)
        (completionInput (fun j => x (swapSeed j)) (wireSwap i)) := by
    have hv := seed_swap_rel x i
    simp only [completionInput, hv]
    apply wireRel_append wireSwap 9 wireSwap_fix wireSwap_lt
    · simp [seed_length]
    · simp [seed_length]
    · exact seed_swap_rel x

  have completion_eval_swap (C : Circuit) (x : Fin 9 → Bool) (i : ℕ) :
      (renameCircuit wireSwap C).eval
          (completionInput (fun j => x (swapSeed j)) (wireSwap i)) =
        C.eval (completionInput x i) := by
    apply eval_rename wireSwap 9 wireSwap_fix wireSwap_lt
    · simp [completionInput, seed_length]
    · simp [completionInput, seed_length]
    · exact completionInput_swap_rel x i

  let canonicalFails (i : ℕ) : Prop :=
    ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (completionInput x i) ≠ target x

  have canonicalFails_swap (i : ℕ) (h : canonicalFails (wireSwap i)) :
      canonicalFails i := by
    intro C hf hs
    have hrf := fanInTwo_rename wireSwap C hf
    have hrs : (renameCircuit wireSwap C).size ≤ 13 := by
      simpa only [size_rename] using hs
    obtain ⟨y, hy⟩ := h (renameCircuit wireSwap C) hrf hrs
    let x : Fin 9 → Bool := fun j => y (swapSeed j)
    refine ⟨x, ?_⟩
    have he := completion_eval_swap C x i
    have hxx : (fun j => x (swapSeed j)) = y := by
      funext j
      exact congrArg y (swapSeed_involution j)
    rw [hxx] at he
    have ht : target x = target y := target_swapSeed y
    rw [← he, ht]
    exact hy

  have completionFails_swap (i : ℕ) (h : completionFails [wireSwap i]) :
      completionFails [i] := by
    exact canonicalFails_swap i h

  have eight_reduction :
      (∀ i : Fin 11, completionFails [i.val]) ↔
        completionFails [0] ∧ completionFails [1] ∧ completionFails [3] ∧
        completionFails [4] ∧ completionFails [6] ∧ completionFails [8] ∧
        completionFails [9] ∧ completionFails [10] := by
    constructor
    · intro h
      exact ⟨h 0, h 1, h 3, h 4, h 6, h 8, h 9, h 10⟩
    · rintro ⟨h0, h1, h3, h4, h6, h8, h9, h10⟩ ⟨i, hi⟩
      have h2 : completionFails [2] := completionFails_swap 2
        (by simpa [wireSwap, swapSeed] using h0)
      have h5 : completionFails [5] := completionFails_swap 5
        (by simpa [wireSwap, swapSeed] using h3)
      have h7 : completionFails [7] := completionFails_swap 7
        (by simpa [wireSwap, swapSeed] using h4)
      interval_cases i <;> assumption
  have h0 : completionFails [0] := group0 0 (by simp)
  have h1 : completionFails [1] := group0 1 (by simp)
  have h3 : completionFails [3] := group0 3 (by simp)
  have h4 : completionFails [4] := group1 4 (by simp)
  have h6 : completionFails [6] := group1 6 (by simp)
  have h8 : completionFails [8] := group1 8 (by simp)
  have h9 : completionFails [9] := group2 9 (by simp)
  have h10 : completionFails [10] := group2 10 (by simp)
  exact finite_reduction.mpr
    (eight_reduction.mpr ⟨h0, h1, h3, h4, h6, h8, h9, h10⟩)
