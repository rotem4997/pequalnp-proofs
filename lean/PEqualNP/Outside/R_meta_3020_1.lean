import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.R_meta_3020_1
    (hFull : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) 14)
    (hZero : ∀ (x1 : List (Fin (11 : ℕ))),   x1 ∈ ([[0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8]] : List (List (Fin (11 : ℕ)))) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hRest : ∀ (x1 : List (Fin (11 : ℕ))),   x1 ∈ ([[1, 3], [1, 4], [1, 6], [1, 8], [3, 4], [3, 5], [3, 6], [3, 7], [3, 8], [4, 6], [4, 7], [4, 8], [6, 8]] : List (List (Fin (11 : ℕ)))) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hNine : ∀ (x1 : List (Fin (11 : ℕ))),   x1 ∈ ([[1, 9], [3, 9], [4, 9], [6, 9], [8, 9]] : List (List (Fin (11 : ℕ)))) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  have cls : ∀ a b : Fin 11,
      (a = b ∨ a = 10 ∨ b = 10 ∨ ((a = 0 ∨ a = 2) ∧ b = 9) ∨ (a = 9 ∧ (b = 0 ∨ b = 2))) ∨
      ∃ i : Fin 2, a.val < 10 ∧ b.val < 10 ∧
        ([(![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i a, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i b] ∈ (([[0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8]] : List (List (Fin 11))) ++ [[1, 3], [1, 4], [1, 6], [1, 8], [3, 4], [3, 5], [3, 6], [3, 7], [3, 8], [4, 6], [4, 7], [4, 8], [6, 8]] ++ [[1, 9], [3, 9], [4, 9], [6, 9], [8, 9]]) ∨
         [(![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i b, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i a] ∈ (([[0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [0, 6], [0, 7], [0, 8]] : List (List (Fin 11))) ++ [[1, 3], [1, 4], [1, 6], [1, 8], [3, 4], [3, 5], [3, 6], [3, 7], [3, 8], [4, 6], [4, 7], [4, 8], [6, 8]] ++ [[1, 9], [3, 9], [4, 9], [6, 9], [8, 9]])) := by
    decide
  have cons9 : ∀ i : Fin 2, ∀ j : Fin 9,
      (((![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i ⟨j.val, by omega⟩ : Fin 11) : ℕ) = (((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i j : Fin 9) : ℕ) := by
    decide
  have fix9 : ∀ i : Fin 2, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i 9 = 9 := by decide
  have fix10 : ∀ i : Fin 2, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i 10 = 10 := by decide
  have pf03 : ∀ i : Fin 2, ((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i 0 = 0 ∧ (![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i 2 = 2) ∨ ((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i 0 = 2 ∧ (![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i 2 = 0) := by
    decide
  intro xs hlen C fan hsize
  refine Classical.byContradiction fun hall => ?_
  have hcomp : ∀ x5 : Fin 9 → Bool, C.eval ((List.ofFn x5 ++ [x5 0 || x5 2]) ++
      [PEqualNP.CircuitLowerBounds.GateOp.and.eval
        (List.map (fun (x8 : Fin 11) => (List.ofFn x5 ++ [x5 0 || x5 2]).getD (↑x8) false) xs)]) =
      (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) := by
    intro x5; by_contra hne; exact hall ⟨x5, hne⟩
  have hsmall : C.gates.length ≤ 13 := hsize
  let F : (Fin 9 → Bool) → Bool := fun x5 => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))
  let W : (Fin 9 → Bool) → List Bool := fun x5 => List.ofFn x5 ++ [x5 0 || x5 2]
  let v : (Fin 9 → Bool) → Bool := fun x5 =>
    PEqualNP.CircuitLowerBounds.GateOp.and.eval
      (List.map (fun (x7 : Fin 11) => (W x5).getD (↑x7) false) xs)
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hc : ∀ x, (C.gates.foldl step (W x ++ [v x])).getD C.output false = F x :=
    fun x => hcomp x
  have hWlen : ∀ x, (W x).length = 10 := by intro x; simp [W]
  have snoc_lt : ∀ (l : List Bool) (a : Bool) (k : ℕ), k < l.length →
      (l ++ [a]).getD k false = l.getD k false :=
    fun l a k h => List.getD_append _ _ _ _ h
  have snoc_eq : ∀ (l : List Bool) (a : Bool) (k : ℕ), k = l.length →
      (l ++ [a]).getD k false = a := by
    intro l a k h; subst h; simp
  have big : ∀ (l : List Bool) (k : ℕ), l.length ≤ k → l.getD k false = false :=
    fun l k h => List.getD_eq_default _ _ h
  have snoc_gt : ∀ (l : List Bool) (a : Bool) (k : ℕ), l.length < k →
      (l ++ [a]).getD k false = false := by
    intro l a k h; exact big _ _ (by simp; omega)
  have getD_W : ∀ x (k : ℕ) (hk : k < 9), (W x).getD k false = x ⟨k, hk⟩ := by
    intro x k hk
    show (List.ofFn x ++ [x 0 || x 2]).getD k false = x ⟨k, hk⟩
    rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hk),
      List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hk]
  have getD_W9 : ∀ x, (W x).getD 9 false = (x 0 || x 2) := by
    intro x; simp [W, List.getD_eq_getElem?_getD]
  have getD_Wbig : ∀ x (k : ℕ), 10 ≤ k → (W x).getD k false = false := by
    intro x k hk; exact big _ _ (by rw [hWlen]; exact hk)
  have gW0 : ∀ x, (W x).getD ((0 : Fin 11) : ℕ) false = x 0 := fun x => getD_W x 0 (by norm_num)
  have gW2 : ∀ x, (W x).getD ((2 : Fin 11) : ℕ) false = x 2 := fun x => getD_W x 2 (by norm_num)
  have gW9 : ∀ x, (W x).getD ((9 : Fin 11) : ℕ) false = (x 0 || x 2) := fun x => getD_W9 x
  have Fzero : F (fun _ => false) = false := rfl
  have and2 : ∀ u w : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, w] = (u && w) := by
    intro u w; cases u <;> cases w <;> rfl
  have or2 : ∀ u w : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, w] = (u || w) := by
    intro u w; cases u <;> cases w <;> rfl
  have first : ∀ x, step (List.ofFn x) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ = W x := by
    intro x
    show List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
      [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false]] = List.ofFn x ++ [x 0 || x 2]
    rw [or2]
    simp [List.getD_eq_getElem?_getD]
  have sim : ∀ (P : List Bool → List Bool → Prop)
      (T : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate)
      (L : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, ∀ A B, P A B → B.length < L →
        (T g).op.eval ((T g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false)) →
      (∀ A B (a : Bool), P A B → B.length < L → P (A ++ [a]) (B ++ [a])) →
      ∀ A B, P A B → B.length + gs.length ≤ L →
        P (gs.foldl step A) ((gs.map T).foldl step B) := by
    intro P T L gs hg hp
    induction gs with
    | nil => intro A B h _; simpa using h
    | cons g gs ih =>
      intro A B h hl
      simp only [List.length_cons] at hl
      have hlt : B.length < L := by omega
      have e := hg g List.mem_cons_self A B h hlt
      simp only [List.foldl_cons, List.map_cons]
      apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      · show P (A ++ [_]) (B ++ [_])
        rw [e]; exact hp A B _ h hlt
      · simp only [step, List.length_append, List.length_singleton]; omega
  have copy_case : ∀ r : ℕ, (∀ x, v x = (W x).getD r false) → False := by
    intro r hr
    let BIG := 11 + C.gates.length
    let r' := if r < 10 then r else BIG
    have hr' : ∀ x, v x = (W x).getD r' false := by
      intro x
      rw [hr x]
      by_cases h : r < 10
      · have e : r' = r := by simp [r', h]
        rw [e]
      · have e : r' = BIG := by simp [r', h]
        rw [e, getD_Wbig x r (by omega), getD_Wbig x BIG (by omega)]
    let ρ : ℕ → ℕ := fun k => if k < 10 then k else if k = 10 then r' else k - 1
    let T : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => ⟨g.op, g.inputs.map ρ⟩
    let P : List Bool → List Bool → Prop := fun A B =>
      A.length = B.length + 1 ∧ 10 ≤ B.length ∧ ∀ k, A.getD k false = B.getD (ρ k) false
    have hgate : ∀ g ∈ C.gates, ∀ A B, P A B → B.length < BIG →
        (T g).op.eval ((T g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) := by
      intro g _ A B h _
      simp only [T, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h.2.2 i).symm
    have hpres : ∀ A B (a : Bool), P A B → B.length < BIG → P (A ++ [a]) (B ++ [a]) := by
      intro A B a h hB
      obtain ⟨hl, h10, hk⟩ := h
      refine ⟨by simp [hl], by simp; omega, ?_⟩
      intro k
      have hk' := hk k
      by_cases h1 : k < 10
      · have e : ρ k = k := by simp [ρ, h1]
        rw [e] at hk' ⊢
        rw [snoc_lt A a k (by omega), snoc_lt B a k (by omega)]; exact hk'
      · by_cases h2 : k = 10
        · subst h2
          by_cases h3 : r < 10
          · have e : ρ 10 = r := by simp [ρ, r', h3]
            rw [e] at hk' ⊢
            rw [snoc_lt A a 10 (by omega), snoc_lt B a r (by omega)]; exact hk'
          · have e : ρ 10 = BIG := by simp [ρ, r', h3]
            rw [e] at hk' ⊢
            rw [big B BIG (by omega)] at hk'
            rw [snoc_lt A a 10 (by omega), snoc_gt B a BIG (by omega)]; exact hk'
        · have e : ρ k = k - 1 := by simp [ρ, h1, h2]
          rw [e] at hk' ⊢
          by_cases h4 : k < A.length
          · rw [snoc_lt A a k h4, snoc_lt B a (k - 1) (by omega)]; exact hk'
          · by_cases h5 : k = A.length
            · rw [snoc_eq A a k h5, snoc_eq B a (k - 1) (by omega)]
            · rw [snoc_gt A a k (by omega), snoc_gt B a (k - 1) (by omega)]
    have hstart : ∀ x, P (W x ++ [v x]) (W x) := by
      intro x
      refine ⟨by simp [hWlen], by simp [hWlen], ?_⟩
      intro k
      by_cases h1 : k < 10
      · have e : ρ k = k := by simp [ρ, h1]
        rw [e, snoc_lt _ _ k (by rw [hWlen]; exact h1)]
      · by_cases h2 : k = 10
        · subst h2
          have e : ρ 10 = r' := by simp [ρ]
          rw [e, snoc_eq _ _ 10 (hWlen x).symm]; exact hr' x
        · have e : ρ k = k - 1 := by simp [ρ, h1, h2]
          rw [e, snoc_gt _ _ k (by rw [hWlen]; omega), big _ (k - 1) (by rw [hWlen]; omega)]
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: C.gates.map T, ρ C.output⟩
    apply hFull
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨g0, hg0, rfl⟩
      · simp
      · have h := fan g0 hg0
        simpa [T] using h
    · show (⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: C.gates.map T).length ≤ 14
      simp; omega
    · intro x
      have hP := sim P T BIG C.gates hgate hpres (W x ++ [v x]) (W x) (hstart x)
        (by rw [hWlen]; show 10 + C.gates.length ≤ 11 + C.gates.length; omega)
      have e1 : D.eval (List.ofFn x) =
          ((C.gates.map T).foldl step (W x)).getD (ρ C.output) false := by
        show ((C.gates.map T).foldl step
          (step (List.ofFn x) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩)).getD
            (ρ C.output) false = _
        rw [first]
      rw [e1, ← hP.2.2 C.output]
      exact hc x
  have true_case : (∀ x, v x = true) → False := by
    classical
    intro hv
    let L := 11 + C.gates.length
    let ρ : ℕ → ℕ := fun k => if k < 10 then k else k - 1
    let T : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate := fun g =>
      if 10 ∈ g.inputs then
        (if g.op = PEqualNP.CircuitLowerBounds.GateOp.and then
          ⟨PEqualNP.CircuitLowerBounds.GateOp.and, (g.inputs.filter (fun k => k ≠ 10)).map ρ⟩
        else if g.op = PEqualNP.CircuitLowerBounds.GateOp.or then
          ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩
        else if g.inputs.head? = some 10 then
          ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
        else ⟨g.op, g.inputs.map ρ⟩)
      else ⟨g.op, g.inputs.map ρ⟩
    let P : List Bool → List Bool → Prop := fun A B =>
      A.length = B.length + 1 ∧ 10 ≤ B.length ∧ A.getD 10 false = true ∧
        ∀ k, k ≠ 10 → A.getD k false = B.getD (ρ k) false
    have allf : ∀ (A B : List Bool) (l : List ℕ), A.getD 10 false = true →
        (∀ k, k ≠ 10 → A.getD k false = B.getD (ρ k) false) →
        (l.map fun i => A.getD i false).all id =
          (((l.filter (fun k => k ≠ 10)).map ρ).map fun i => B.getD i false).all id := by
      intro A B l h10 hk
      induction l with
      | nil => rfl
      | cons k l ih =>
        by_cases hk10 : k = 10
        · subst hk10
          have hf : (List.filter (fun k => decide (k ≠ 10)) (10 :: l)) =
              List.filter (fun k => decide (k ≠ 10)) l := by simp
          rw [hf, List.map_cons, List.all_cons, h10, id, Bool.true_and]
          exact ih
        · have hf : (List.filter (fun k => decide (k ≠ 10)) (k :: l)) =
              k :: List.filter (fun k => decide (k ≠ 10)) l := by simp [hk10]
          rw [hf, List.map_cons, List.map_cons, List.map_cons, List.all_cons, List.all_cons,
            hk k hk10, ih]
    have hgate : ∀ g ∈ C.gates, ∀ A B, P A B → B.length < L →
        (T g).op.eval ((T g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) := by
      intro g hg A B h _
      obtain ⟨_, _, h10, hk⟩ := h
      have hop := (fan g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      by_cases hin : 10 ∈ g.inputs
      · rcases hop with hop | hop | hop
        · have eT : T g = ⟨PEqualNP.CircuitLowerBounds.GateOp.and,
              (g.inputs.filter (fun k => k ≠ 10)).map ρ⟩ := by
            simp only [T, hin, hop, ↓reduceIte]
          rw [eT, hop]
          exact (allf A B g.inputs h10 hk).symm
        · have eT : T g = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ := by
            simp only [T, hin, hop, reduceCtorEq, ↓reduceIte]
          rw [eT, hop]
          change true = (List.map (fun i => A.getD i false) g.inputs).any id
          symm
          rw [List.any_eq_true]
          exact ⟨true, List.mem_map.2 ⟨10, hin, h10⟩, rfl⟩
        · by_cases hh : g.inputs.head? = some 10
          · have eT : T g = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
              simp only [T, hin, hop, hh, reduceCtorEq, ↓reduceIte]
            obtain ⟨rest, hr⟩ : ∃ rest, g.inputs = 10 :: rest := by
              cases hgi : g.inputs with
              | nil => rw [hgi] at hh; simp at hh
              | cons a rest => rw [hgi] at hh; simp at hh; exact ⟨rest, by rw [hh]⟩
            rw [eT, hop, hr]
            change false = !((List.map (fun i => A.getD i false) (10 :: rest)).headD false)
            simp only [List.map_cons, List.headD_cons, h10, Bool.not_true]
          · have eT : T g = ⟨g.op, g.inputs.map ρ⟩ := by
              simp only [T, hin, hop, hh, reduceCtorEq, ↓reduceIte]
            rw [eT, hop]
            cases hgi : g.inputs with
            | nil => rfl
            | cons a rest =>
              have ha : a ≠ 10 := by rw [hgi] at hh; simpa using hh
              change (!((List.map (fun i => B.getD i false) (List.map ρ (a :: rest))).headD false)) =
                !((List.map (fun i => A.getD i false) (a :: rest)).headD false)
              simp only [List.map_cons, List.headD_cons]
              rw [hk a ha]
      · have eT : T g = ⟨g.op, g.inputs.map ρ⟩ := by
          simp only [T, hin, ↓reduceIte]
        rw [eT]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hi10 : i ≠ 10 := fun e => hin (e ▸ hi)
        exact (hk i hi10).symm
    have hpres : ∀ A B (a : Bool), P A B → B.length < L → P (A ++ [a]) (B ++ [a]) := by
      intro A B a h hB
      obtain ⟨hl, h10, hA10, hk⟩ := h
      refine ⟨by simp [hl], by simp; omega, ?_, ?_⟩
      · rw [snoc_lt A a 10 (by omega)]; exact hA10
      intro k hk10
      have hk' := hk k hk10
      by_cases h1 : k < 10
      · have e : ρ k = k := by simp [ρ, h1]
        rw [e] at hk' ⊢
        rw [snoc_lt A a k (by omega), snoc_lt B a k (by omega)]; exact hk'
      · have e : ρ k = k - 1 := by simp [ρ, h1]
        rw [e] at hk' ⊢
        by_cases h4 : k < A.length
        · rw [snoc_lt A a k h4, snoc_lt B a (k - 1) (by omega)]; exact hk'
        · by_cases h5 : k = A.length
          · rw [snoc_eq A a k h5, snoc_eq B a (k - 1) (by omega)]
          · rw [snoc_gt A a k (by omega), snoc_gt B a (k - 1) (by omega)]
    have hstart : ∀ x, P (W x ++ [v x]) (W x) := by
      intro x
      refine ⟨by simp [hWlen], by simp [hWlen], ?_, ?_⟩
      · rw [snoc_eq _ _ 10 (hWlen x).symm]; exact hv x
      intro k hk10
      by_cases h1 : k < 10
      · have e : ρ k = k := by simp [ρ, h1]
        rw [e, snoc_lt _ _ k (by rw [hWlen]; exact h1)]
      · have e : ρ k = k - 1 := by simp [ρ, h1]
        rw [e, snoc_gt _ _ k (by rw [hWlen]; omega), big _ (k - 1) (by rw [hWlen]; omega)]
    have run : ∀ x, P (C.gates.foldl step (W x ++ [v x])) ((C.gates.map T).foldl step (W x)) :=
      fun x => sim P T L C.gates hgate hpres _ _ (hstart x)
        (by rw [hWlen]; show 10 + C.gates.length ≤ 11 + C.gates.length; omega)
    by_cases hout : C.output = 10
    · have h := hc (fun _ => false)
      rw [hout, (run (fun _ => false)).2.2.1, Fzero] at h
      exact Bool.noConfusion h
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: C.gates.map T, ρ C.output⟩
    apply hFull
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      simp only [D, List.mem_cons, List.mem_map] at hg
      rcases hg with rfl | ⟨g0, hg0, rfl⟩
      · simp
      · have h := fan g0 hg0
        have hop := h.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        by_cases hin : 10 ∈ g0.inputs
        · rcases hop with hop | hop | hop
          · have eT : T g0 = ⟨PEqualNP.CircuitLowerBounds.GateOp.and,
                (g0.inputs.filter (fun k => k ≠ 10)).map ρ⟩ := by
              simp only [T, hin, hop, ↓reduceIte]
            rw [eT]
            refine ⟨by simp, ?_⟩
            show ((g0.inputs.filter (fun k => k ≠ 10)).map ρ).length ≤ 2
            rw [List.length_map]
            exact le_trans (List.length_filter_le _ _) h.2
          · have eT : T g0 = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ := by
              simp only [T, hin, hop, reduceCtorEq, ↓reduceIte]
            rw [eT]
            exact ⟨by simp, by simp⟩
          · by_cases hh : g0.inputs.head? = some 10
            · have eT : T g0 = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
                simp only [T, hin, hop, hh, reduceCtorEq, ↓reduceIte]
              rw [eT]
              exact ⟨by simp, by simp⟩
            · have eT : T g0 = ⟨g0.op, g0.inputs.map ρ⟩ := by
                simp only [T, hin, hop, hh, reduceCtorEq, ↓reduceIte]
              rw [eT]
              exact ⟨h.1, by simpa using h.2⟩
        · have eT : T g0 = ⟨g0.op, g0.inputs.map ρ⟩ := by
            simp only [T, hin, ↓reduceIte]
          rw [eT]
          exact ⟨h.1, by simpa using h.2⟩
    · show (⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: C.gates.map T).length ≤ 14
      simp; omega
    · intro x
      have e1 : D.eval (List.ofFn x) =
          ((C.gates.map T).foldl step (W x)).getD (ρ C.output) false := by
        show ((C.gates.map T).foldl step
          (step (List.ofFn x) ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩)).getD
            (ρ C.output) false = _
        rw [first]
      rw [e1, ← (run x).2.2.2 C.output hout]
      exact hc x
  have sym : ∀ (i : Fin 2) (p q : Fin 11), p.val < 10 → q.val < 10 →
      (∀ x, v x = ((W x).getD p false && (W x).getD q false)) →
      ∀ Lst : List (List (Fin 11)),
      (∀ (x1 : List (Fin 11)), x1 ∈ Lst → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ 13 →
        ∃ x6 : Fin 9 → Bool, x3.eval (W x6 ++
          [PEqualNP.CircuitLowerBounds.GateOp.and.eval
            (List.map (fun (x8 : Fin 11) => (W x6).getD (↑x8) false) x1)]) ≠ F x6) →
      [(![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i p, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i q] ∈ Lst → False := by
    intro i p q hp hq hv Lst H mem
    have inv : ∀ x : Fin 9 → Bool, F (fun j => x ((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i j)) = F x := by
      intro x
      fin_cases i
      · have hb : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) = (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by decide
        exact hb (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
      · have hb : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, (b2 && b1 || b1 && b0 || b0 && b5 || b5 && b7 || b7 && b2 || b2 && b3 || b1 && b6 || b0 && b4 || b5 && b8 || b3 && b4 || b6 && b8 || b8 && b3) = (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 || b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by decide
        exact hb (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    let τ : ℕ → ℕ := fun k => if h : k < 11 then (((![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i ⟨k, h⟩ : Fin 11) : ℕ) else k
    have τlt : ∀ k, k < 11 → τ k < 11 := by
      intro k hk; simp only [τ, dif_pos hk]; exact Fin.isLt _
    have τge : ∀ k, 11 ≤ k → τ k = k := by
      intro k hk; simp only [τ, dif_neg (show ¬ k < 11 by omega)]
    have τfin : ∀ a : Fin 11, τ a = (((![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i a : Fin 11) : ℕ) := by
      intro a; simp only [τ, dif_pos a.isLt]
    have τ9 : τ 9 = 9 := by
      simp only [τ, dif_pos (show (9 : ℕ) < 11 by norm_num)]
      exact congrArg Fin.val (fix9 i)
    have τ10 : τ 10 = 10 := by
      simp only [τ, dif_pos (show (10 : ℕ) < 11 by norm_num)]
      exact congrArg Fin.val (fix10 i)
    have τsmall : ∀ k (hk : k < 9), τ k = (((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i ⟨k, hk⟩ : Fin 9) : ℕ) := by
      intro k hk
      have := cons9 i ⟨k, hk⟩
      simp only [τ, dif_pos (show k < 11 by omega)]
      exact this
    let y : (Fin 9 → Bool) → (Fin 9 → Bool) := fun x j => x ((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i j)
    have base : ∀ x k, k < 10 → (W (y x)).getD k false = (W x).getD (τ k) false := by
      intro x k hk
      by_cases h9 : k < 9
      · rw [getD_W _ k h9, τsmall k h9, getD_W _ _ ((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i ⟨k, h9⟩).isLt] <;> rfl
      · have e : k = 9 := by omega
        subst e
        rw [τ9, getD_W9, getD_W9]
        rcases pf03 i with ⟨h0, h3⟩ | ⟨h0, h3⟩
        · simp only [y, h0, h3]
        · simp only [y, h0, h3, Bool.or_comm]
    have τW : ∀ k, k < 10 → τ k < 10 := by
      intro k hk
      by_cases h9 : k < 9
      · rw [τsmall k h9]; have := ((![![0, 1, 2, 3, 4, 5, 6, 7, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8]] : Fin 2 → Fin 9 → Fin 9) i ⟨k, h9⟩).isLt; omega
      · rw [show k = 9 by omega, τ9]; omega
    let T : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => ⟨g.op, g.inputs.map τ⟩
    let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map T, τ C.output⟩
    let P : List Bool → List Bool → Prop := fun A B =>
      A.length = B.length ∧ 11 ≤ A.length ∧ ∀ k, A.getD k false = B.getD (τ k) false
    have hgate : ∀ g ∈ C.gates, ∀ A B, P A B → B.length < 1000 →
        (T g).op.eval ((T g).inputs.map fun i => B.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) := by
      intro g _ A B h _
      simp only [T, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h.2.2 i).symm
    have hpres : ∀ A B (a : Bool), P A B → B.length < 1000 → P (A ++ [a]) (B ++ [a]) := by
      intro A B a h _
      obtain ⟨hl, h11, hk⟩ := h
      refine ⟨by simp [hl], by simp; omega, ?_⟩
      intro k
      have hk' := hk k
      by_cases h1 : k < 11
      · have := τlt k h1
        rw [snoc_lt A a k (by omega), snoc_lt B a (τ k) (by omega)]; exact hk'
      · rw [τge k (by omega)] at hk' ⊢
        by_cases h5 : k = A.length
        · rw [snoc_eq A a k h5, snoc_eq B a k (by omega)]
        · by_cases h4 : k < A.length
          · rw [snoc_lt A a k h4, snoc_lt B a k (by omega)]; exact hk'
          · rw [snoc_gt A a k (by omega), snoc_gt B a k (by omega)]
    have comp : ∀ x5 : Fin 9 → Bool, C'.eval (W x5 ++
        [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun (x7 : Fin 11) => (W x5).getD (↑x7) false) [(![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i p, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i q])]) =
          F x5 := by
      intro x
      have h0 : P (W (y x) ++ [v (y x)]) (W x ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun (x7 : Fin 11) => (W x).getD (↑x7) false) [(![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i p, (![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9, 10]] : Fin 2 → Fin 11 → Fin 11) i q])]) := by
        refine ⟨by simp [hWlen], by simp [hWlen], ?_⟩
        intro k
        by_cases h1 : k < 10
        · have := τW k h1
          rw [snoc_lt _ _ k (by rw [hWlen]; exact h1), snoc_lt _ _ (τ k) (by rw [hWlen]; exact this)]
          exact base x k h1
        · by_cases h2 : k = 10
          · subst h2
            rw [τ10, snoc_eq _ _ 10 (hWlen _).symm, snoc_eq _ _ 10 (hWlen _).symm]
            rw [hv (y x), base x p hp, base x q hq, τfin p, τfin q]
            exact (and2 _ _).symm
          · rw [τge k (by omega), snoc_gt _ _ k (by rw [hWlen]; omega),
              snoc_gt _ _ k (by rw [hWlen]; omega)]
      have hP := sim P T 1000 C.gates hgate hpres _ _ h0 (by simp [hWlen]; omega)
      show ((C.gates.map T).foldl step _).getD (τ C.output) false = F x
      rw [← hP.2.2 C.output, hc (y x)]
      exact inv x
    have hfan : PEqualNP.MetaComplexity.FanInTwo C' := by
      intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have h := fan g0 hg0
      exact ⟨h.1, by simpa [T] using h.2⟩
    have hs' : C'.size ≤ 13 := by
      show (C.gates.map T).length ≤ 13
      rw [List.length_map]; exact hsmall
    obtain ⟨x6, hx6⟩ := H _ mem C' hfan hs'
    exact hx6 (comp x6)
  have ev0 : ∀ (x : Fin 9 → Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval [] = true ∧
      ∀ (u : Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval [u] = u ∧
      ∀ (w : Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval [u, w] = (u && w) := by
    intro _
    refine ⟨rfl, fun u => ⟨by cases u <;> rfl, fun w => by cases u <;> cases w <;> rfl⟩⟩
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact true_case (fun x => (ev0 x).1)
  · exact copy_case a (fun x => ((ev0 x).2 _).1)
  · have hvab : ∀ x, v x = ((W x).getD a false && (W x).getD b false) :=
      fun x => (((ev0 x).2 _).2 _)
    rcases cls a b with deg | ⟨i, ha, hb, h⟩
    · by_cases hab : a = b
      · subst hab
        exact copy_case a (fun x => by rw [hvab x, Bool.and_self])
      rcases deg with deg | deg | deg | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact absurd deg hab
      · subst deg
        exact copy_case 10 (fun x => by
          rw [hvab x, getD_Wbig x ((10 : Fin 11) : ℕ) (by decide), getD_Wbig x 10 le_rfl,
            Bool.false_and])
      · subst deg
        exact copy_case 10 (fun x => by
          rw [hvab x, getD_Wbig x ((10 : Fin 11) : ℕ) (by decide), getD_Wbig x 10 le_rfl,
            Bool.and_false])
      · subst hb
        refine copy_case a (fun x => ?_)
        rw [hvab x, gW9]
        rcases ha with rfl | rfl
        · rw [gW0]; generalize x 0 = u; generalize x 2 = w; revert u w; decide
        · rw [gW2]; generalize x 0 = u; generalize x 2 = w; revert u w; decide
      · subst ha
        refine copy_case b (fun x => ?_)
        rw [hvab x, gW9]
        rcases hb with rfl | rfl
        · rw [gW0]; generalize x 0 = u; generalize x 2 = w; revert u w; decide
        · rw [gW2]; generalize x 0 = u; generalize x 2 = w; revert u w; decide
    · have hv : ∀ x, v x = ((W x).getD a false && (W x).getD b false) := hvab
      have hv' : ∀ x, v x = ((W x).getD b false && (W x).getD a false) := by
        intro x; rw [hv x, Bool.and_comm]
      rcases h with h | h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · exact sym i a b ha hb hv _ hZero h
          · exact sym i a b ha hb hv _ hRest h
        · exact sym i a b ha hb hv _ hNine h
      · rcases List.mem_append.1 h with h | h
        · rcases List.mem_append.1 h with h | h
          · exact sym i b a hb ha hv' _ hZero h
          · exact sym i b a hb ha hv' _ hRest h
        · exact sym i b a hb ha hv' _ hNine h
  · simp at hlen
