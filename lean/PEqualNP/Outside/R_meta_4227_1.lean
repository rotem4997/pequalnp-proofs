import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- Remove the four surviving lines through point 0. Their nonzero point neighborhoods
-- partition the sixteen affine points. Keep a reserve wire for each neighborhood.
-- Each restored line costs three gates: its point OR, its AND, and an output OR.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.R_meta_4227_1
    (core :
      let I := fun (u v : Fin 42) => u.val < 21 ∧ 21 < v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let restored : List (Fin 42) := [26, 28, 38, 41]
      ∃ (D : Circuit) (a b c d : ℕ), Monotone2 D ∧ ReadsBack 42 D ∧
        D.size ≤ 106 ∧ D.output < 42 + D.size ∧
        a < 42 + D.size ∧ b < 42 + D.size ∧ c < 42 + D.size ∧ d < 42 + D.size ∧
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 42, I u v ∧ v ∉ restored ∧ x u = true ∧ x v = true) ∧
        ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = false →
          let W := D.wires (List.ofFn x)
          W.getD a false = ([5, 6, 9, 19] : List (Fin 42)).any x ∧
          W.getD b false = ([2, 7, 8, 11] : List (Fin 42)).any x ∧
          W.getD c false = ([10, 12, 17, 18] : List (Fin 42)).any x ∧
          W.getD d false = ([3, 13, 15, 20] : List (Fin 42)).any x)
    (appendLine :
      ∀ (n : ℕ) (p l : Fin n) (D : Circuit) (j : ℕ), Monotone2 D → ReadsBack n D →
        D.output < n + D.size → j < n + D.size →
        ∃ E : Circuit, Monotone2 E ∧ ReadsBack n E ∧
          E.size = D.size + 3 ∧ E.output < n + E.size ∧
          (∀ i < n + D.size, ∀ x : Fin n → Bool,
            (E.wires (List.ofFn x)).getD i false = (D.wires (List.ofFn x)).getD i false) ∧
          ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
            (D.eval (List.ofFn x) || (x l && (x p || (D.wires (List.ofFn x)).getD j false)))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (42 : ℕ) x1 ∧ x1.output < (42 : ℕ) + x1.size ∧ x1.size ≤ (118 : ℕ) ∧ (∀ (x2 : Fin (42 : ℕ)), ↑x2 ∈ [(0 : ℕ), (1 : ℕ), (4 : ℕ), (14 : ℕ)] → ∃ x4 ∈ x1.gates, ↑x2 ∈ x4.inputs) ∧ ∀ (x2 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (42 : ℕ)) (x4 : Fin (42 : ℕ)), (↑x3 < (21 : ℕ) ∧ (21 : ℕ) < ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true := by
  obtain ⟨D, a, b, c, d, base, back, size, output, ba, bb, bc, bd, relation, reserve⟩ := core
  obtain ⟨C1, m1, k1, s1, o1, keep1, val1⟩ :=
    appendLine 42 0 26 D a base back output ba
  obtain ⟨C2, m2, k2, s2, o2, keep2, val2⟩ :=
    appendLine 42 0 28 C1 b m1 k1 o1 (by omega)
  obtain ⟨C3, m3, k3, s3, o3, keep3, val3⟩ :=
    appendLine 42 0 38 C2 c m2 k2 o2 (by omega)
  obtain ⟨C4, m4, k4, s4, o4, _, val4⟩ :=
    appendLine 42 0 41 C3 d m3 k3 o3 (by omega)
  let I := fun (u v : Fin 42) => u.val < 21 ∧ 21 < v.val ∧
    (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  let S : List (Fin 42) := [26, 28, 38, 41]
  let A : List (Fin 42) := [5, 6, 9, 19]
  let B : List (Fin 42) := [2, 7, 8, 11]
  let C : List (Fin 42) := [10, 12, 17, 18]
  let F : List (Fin 42) := [3, 13, 15, 20]
  have line26 (u : Fin 42) : I u 26 ↔ u = 0 ∨ u ∈ A := by
    fin_cases u <;> decide +kernel
  have line28 (u : Fin 42) : I u 28 ↔ u = 0 ∨ u ∈ B := by
    fin_cases u <;> decide +kernel
  have line38 (u : Fin 42) : I u 38 ↔ u = 0 ∨ u ∈ C := by
    fin_cases u <;> decide +kernel
  have line41 (u : Fin 42) : I u 41 ↔ u = 0 ∨ u ∈ F := by
    fin_cases u <;> decide +kernel
  have partition : ∀ u v : Fin 42, I u v ↔
      (((I u v ∧ v ∉ S) ∨ (v = 26 ∧ (u = 0 ∨ u ∈ A))) ∨
        (v = 28 ∧ (u = 0 ∨ u ∈ B))) ∨
        (v = 38 ∧ (u = 0 ∨ u ∈ C)) ∨ (v = 41 ∧ (u = 0 ∨ u ∈ F)) := by
    intro u v
    by_cases v26 : v = 26
    · subst v
      simpa [S] using line26 u
    · by_cases v28 : v = 28
      · subst v
        simpa [S] using line28 u
      · by_cases v38 : v = 38
        · subst v
          simpa [S] using line38 u
        · by_cases v41 : v = 41
          · subst v
            simpa [S] using line41 u
          · simp [S, v26, v28, v38, v41]
  let chosen := fun (x : Fin 42 → Bool) (v : Fin 42) (N : List (Fin 42)) =>
    x v && (x 0 || N.any x)
  have terms (x : Fin 42 → Bool) (v : Fin 42) (N : List (Fin 42)) :
      chosen x v N = true ↔
        ∃ u : Fin 42, (u = 0 ∨ u ∈ N) ∧ x u = true ∧ x v = true := by
    simp only [chosen, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨hv, h0 | ⟨u, hu, hx⟩⟩
      · exact ⟨0, Or.inl rfl, h0, hv⟩
      · exact ⟨u, Or.inr hu, hx, hv⟩
    · rintro ⟨u, rfl | hu, hx, hv⟩
      · exact ⟨hv, Or.inl hx⟩
      · exact ⟨hv, Or.inr ⟨u, hu, hx⟩⟩
  have value (x : Fin 42 → Bool) : C4.eval (List.ofFn x) =
      (D.eval (List.ofFn x) || chosen x 26 A || chosen x 28 B ||
        chosen x 38 C || chosen x 41 F) := by
    rw [val4, val3, val2, val1]
    rw [keep3 d (by omega), keep2 c (by omega), keep2 d (by omega),
      keep1 b (by omega), keep1 c (by omega), keep1 d (by omega)]
    cases h : D.eval (List.ofFn x) with
    | false =>
      obtain ⟨ha, hb, hc, hd⟩ := reserve x h
      rw [ha, hb, hc, hd]
    | true => simp only [Bool.true_or]
  have correct (x : Fin 42 → Bool) :
      C4.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, I u v ∧ x u = true ∧ x v = true := by
    rw [value]
    simp only [Bool.or_eq_true, relation, terms]
    constructor
    · rintro ((((h | h) | h) | h) | h)
      · obtain ⟨u, v, near, _, hu, hv⟩ := h
        exact ⟨u, v, near, hu, hv⟩
      · obtain ⟨u, hN, hu, hv⟩ := h
        exact ⟨u, 26, (partition u 26).mpr (Or.inl (Or.inl (Or.inr ⟨rfl, hN⟩))), hu, hv⟩
      · obtain ⟨u, hN, hu, hv⟩ := h
        exact ⟨u, 28, (partition u 28).mpr (Or.inl (Or.inr ⟨rfl, hN⟩)), hu, hv⟩
      · obtain ⟨u, hN, hu, hv⟩ := h
        exact ⟨u, 38, (partition u 38).mpr (Or.inr (Or.inl ⟨rfl, hN⟩)), hu, hv⟩
      · obtain ⟨u, hN, hu, hv⟩ := h
        exact ⟨u, 41, (partition u 41).mpr (Or.inr (Or.inr ⟨rfl, hN⟩)), hu, hv⟩
    · rintro ⟨u, v, close, hu, hv⟩
      rcases (partition u v).mp close with (((h | ⟨rfl, h⟩) | ⟨rfl, h⟩) | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨u, v, h.1, h.2, hu, hv⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨u, h, hu, hv⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨u, h, hu, hv⟩))
      · exact Or.inl (Or.inr ⟨u, h, hu, hv⟩)
      · exact Or.inr ⟨u, h, hu, hv⟩
  refine ⟨C4, m4, k4, o4, by omega, ?_, correct⟩
  intro i watched
  have neighbor : ∃ l : Fin 42, I i l := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at watched
    rcases watched with h | h | h | h
    · have h0 : i = 0 := Fin.ext h
      subst i
      exact ⟨26, by decide +kernel⟩
    · have h1 : i = 1 := Fin.ext h
      subst i
      exact ⟨22, by decide +kernel⟩
    · have h4 : i = 4 := Fin.ext h
      subst i
      exact ⟨25, by decide +kernel⟩
    · have h14 : i = 14 := Fin.ext h
      subst i
      exact ⟨35, by decide +kernel⟩
  obtain ⟨l, incident⟩ := neighbor
  let single (v : Fin 42) : Fin 42 → Bool := fun t => decide (t = v)
  have singleFalse (v : Fin 42) : C4.eval (List.ofFn (single v)) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨p, q, h, hp, hq⟩ := (correct _).mp he
    simp only [single, decide_eq_true_eq] at hp hq
    subst p
    subst q
    have lo : v.val < 21 := h.1
    have hi : 21 < v.val := h.2.1
    omega
  let pair : Fin 42 → Bool := fun t => decide (t = i ∨ t = l)
  have pairTrue : C4.eval (List.ofFn pair) = true :=
    (correct _).mpr ⟨i, l, incident, by simp [pair], by simp [pair]⟩
  have inValue (x : Fin 42 → Bool) (j : Fin 42) :
      (List.ofFn x).getD j.val false = x j := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn _
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have keepRaw (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hj
  have notOutput : C4.output ≠ i.val := by
    intro index
    have yes : C4.eval (List.ofFn (single i)) = true := by
      change (C4.gates.foldl step (List.ofFn (single i))).getD C4.output false = true
      rw [index, keepRaw _ _ _ (by simp)]
      rw [inValue]
      simp [single]
    exact Bool.noConfusion (yes.symm.trans (singleFalse i))
  by_contra omitted
  have unobserved (g : Gate) (hg : g ∈ C4.gates) : i.val ∉ g.inputs :=
    fun hi => omitted ⟨g, hg, hi⟩
  have agree (j : ℕ) (ne : j ≠ i.val) :
      (List.ofFn pair).getD j false = (List.ofFn (single l)).getD j false := by
    by_cases hj : j < 42
    · let k : Fin 42 := ⟨j, hj⟩
      have nk : k ≠ i := fun eq => ne (congrArg Fin.val eq)
      change (List.ofFn pair).getD k.val false = (List.ofFn (single l)).getD k.val false
      rw [inValue pair k, inValue (single l) k]
      simp only [pair, single, nk, false_or]
    · rw [List.getD_eq_default (List.ofFn pair) _ (by simp; omega),
        List.getD_eq_default (List.ofFn (single l)) _ (by simp; omega)]
  have replay (gs : List Gate) (notRead : ∀ g ∈ gs, i.val ∉ g.inputs)
      (u v : List Bool) (len : u.length = v.length)
      (rows : ∀ j, j ≠ i.val → u.getD j false = v.getD j false) :
      ∀ j, j ≠ i.val → (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
    induction gs generalizing u v with
    | nil => exact rows
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun a ha => notRead a (List.mem_cons_of_mem _ ha))
        (step u g) (step v g) (by simp [step, len])
      intro j hj
      have equalGate : g.op.eval (g.inputs.map fun k => u.getD k false) =
          g.op.eval (g.inputs.map fun k => v.getD k false) := by
        congr 1
        exact List.map_congr_left (fun k hk => rows k (fun eq => notRead g List.mem_cons_self (eq ▸ hk)))
      dsimp only [step]
      rw [equalGate]
      by_cases hk : j < u.length
      · rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ (len ▸ hk)]
        exact rows j hj
      · have outside : u.length ≤ j := Nat.le_of_not_gt hk
        rw [List.getD_append_right _ _ _ _ outside, List.getD_append_right _ _ _ _ (len ▸ outside), len]
  have eq : C4.eval (List.ofFn pair) = C4.eval (List.ofFn (single l)) :=
    replay C4.gates unobserved _ _ (by simp) agree C4.output notOutput
  exact Bool.noConfusion (pairTrue.symm.trans (eq.trans (singleFalse l)))
