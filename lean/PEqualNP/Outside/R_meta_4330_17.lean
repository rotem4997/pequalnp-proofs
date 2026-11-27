import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4330_17
    (findCopies : let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ (A : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool), PEqualNP.MetaComplexity.FanInTwo A → A.size = 18 →
      (∀ x : Fin 10 → Bool, (if b = true then !(A.eval (List.ofFn x)) else A.eval (List.ofFn x)) = F x) →
      ∃ v : Fin 10, ∃ S : Finset (Fin A.gates.length), S.card = 3 ∧
        ∀ j ∈ S, ∃ k : ℕ, k < 10 + j.val ∧ ∀ x : Fin 10 → Bool, x v = false →
          (A.wires (List.ofFn x)).getD (10 + j.val) false =
            (A.wires (List.ofFn x)).getD k false)
    (compress : ∀ (A : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 10), PEqualNP.MetaComplexity.FanInTwo A →
      (∃ S : Finset (Fin A.gates.length), S.card = 3 ∧
        ∀ j ∈ S, ∃ k : ℕ, k < 10 + j.val ∧ ∀ x : Fin 10 → Bool, x v = false →
          (A.wires (List.ofFn x)).getD (10 + j.val) false =
            (A.wires (List.ofFn x)).getD k false) →
      ∃ B : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo B ∧ B.size + 3 ≤ A.size ∧
        ∀ x : Fin 10 → Bool, x v = false → B.eval (List.ofFn x) = A.eval (List.ofFn x))
 :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (17 : ℕ) →         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => (x3.wires ({ gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x4 Bool.false;         (∀ (x10 : Fin (10 : ℕ) → Bool), (if x5 = Bool.true then !x9 x10 else x9 x10) = x1 x10) →           ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : ℕ) (x13 : Bool),             PEqualNP.MetaComplexity.FanInTwo x11 ∧               x11.size ≤ (15 : ℕ) ∧                 have x14 : (Fin (10 : ℕ) → Bool) → Bool := fun (x14 : Fin (10 : ℕ) → Bool) => (x11.wires (List.ofFn x14)).getD x12 Bool.false;                 ∀ (x15 : Fin (10 : ℕ) → Bool), x15 (9 : Fin (10 : ℕ)) = Bool.false → (if x13 = Bool.true then !x14 x15 else x14 x15) = x1 x15 := by
  dsimp only
  intro g T u b hg hT hsize hcorrect
  let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let A : PEqualNP.CircuitLowerBounds.Circuit := ⟨g :: T.gates, u⟩
  have ha : PEqualNP.MetaComplexity.FanInTwo A := by
    intro q hq
    rcases List.mem_cons.mp hq with he | ht
    · subst q
      exact hg _ (List.mem_singleton_self _)
    · exact hT _ ht
  have hs : A.size = 18 := by
    change T.gates.length + 1 = 18
    change T.gates.length = 17 at hsize
    omega
  have spec (x : Fin 10 → Bool) :
      (if b = true then !(A.eval (List.ofFn x)) else A.eval (List.ofFn x)) = F x := hcorrect x
  obtain ⟨v, hc⟩ := findCopies A b ha hs spec
  obtain ⟨B, hb, hcost, he⟩ := compress A v ha hc
  obtain ⟨perm, hperm⟩ : ∃ perm : Fin 10 → Fin 10 → Fin 10, perm = ![![9, 6, 8, 5, 7, 4, 1, 3, 0, 2], ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3], ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3], ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2], ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4], ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] := ⟨_, rfl⟩
  have perm9 : ∀ v : Fin 10, perm v v = 9 := by
    subst hperm; decide
  have PF_bits : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool, ∀ v : Fin 10, F (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] ∘ perm v) = F ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
    subst hperm; unfold F; decide
  have perm_aut : ∀ (v : Fin 10) (x : Fin 10 → Bool), F (x ∘ perm v) = F x := by
    intro v x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
      funext i; fin_cases i <;> rfl
    rw [hx]
    exact PF_bits _ _ _ _ _ _ _ _ _ _ v
  let step : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), List Bool := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), List Bool := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) => gs.foldl step l
  have run_cons : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), run (g :: gs) l = run gs (step l g) := fun g gs l => rfl
  have ofFn_getD' : ∀ (x : Fin 10 → Bool) (i : ℕ), (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
    intro x i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split_ifs <;> simp
  let rlbl : ∀ (π : Fin 10 → Fin 10) (i : ℕ), ℕ := fun (π : Fin 10 → Fin 10) (i : ℕ) => if h : i < 10 then (π ⟨i, h⟩ : ℕ) else i
  let rlblG : ∀ (π : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.CircuitLowerBounds.Gate := fun (π : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate) => ⟨g.op, g.inputs.map (rlbl π)⟩
  have rlbl_run : ∀ (π : Fin 10 → Fin 10) (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (L L' : List Bool), L.length = L'.length → 10 ≤ L.length → (∀ k, L.getD (rlbl π k) false = L'.getD k false) → ∀ k, (run (gs.map (rlblG π)) L).getD (rlbl π k) false = (run gs L').getD k false := by
    intro π gs
    induction gs with
    | nil => intro L L' _ _ h k; exact h k
    | cons g gs ih =>
      intro L L' hlen h10 h
      rw [List.map_cons, run_cons, run_cons]
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · intro k
        simp only [step]
        have hval : (rlblG π g).op.eval ((rlblG π g).inputs.map fun i => L.getD i false) =
            g.op.eval (g.inputs.map fun i => L'.getD i false) := by
          simp only [rlblG, List.map_map, Function.comp_def, h]
        rw [hval]
        by_cases hk : k < 10
        · have hr : rlbl π k = π ⟨k, hk⟩ := by simp [rlbl, hk]
          rw [hr, List.getD_append _ _ _ _ (by have := (π ⟨k, hk⟩).isLt; omega),
            List.getD_append _ _ _ _ (by omega), ← hr]
          exact h k
        · have hr : rlbl π k = k := by simp [rlbl, hk]
          rw [hr]
          by_cases hkl : k < L.length
          · rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (by omega)]
            have := h k
            rwa [hr] at this
          · by_cases hke : k = L.length
            · subst hke
              rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega)]
              simp [hlen]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have renameInputs : ∀ (B : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10), PEqualNP.MetaComplexity.FanInTwo B →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = B.size ∧
        ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = B.eval (List.ofFn (x ∘ σ)) := by
    intro E σ hE
    refine ⟨⟨E.gates.map (rlblG σ), rlbl σ E.output⟩, ?_, List.length_map _, ?_⟩
    · intro g hg
      obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg
      simpa [rlblG] using hE g0 h0
    · intro x
      exact rlbl_run σ E.gates (List.ofFn x) (List.ofFn (x ∘ σ)) (by simp) (by simp) (by
        intro k
        rw [ofFn_getD', ofFn_getD']
        by_cases hk : k < 10 <;> simp [rlbl, hk, Function.comp_apply]) E.output
  obtain ⟨D, hd, hdsize, hdval⟩ := renameInputs B (perm v) hb
  refine ⟨D, D.output, b, hd, by omega, ?_⟩
  intro x hx
  change (if b = true then !(D.eval (List.ofFn x)) else D.eval (List.ofFn x)) = F x
  rw [hdval, he _ (by simp [Function.comp_apply, perm9, hx]), spec, perm_aut]
