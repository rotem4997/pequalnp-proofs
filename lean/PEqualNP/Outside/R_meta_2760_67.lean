import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2760_67
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∀ j : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x j]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∀ a b : Fin 9, ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false,x a || x b]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (h3 : ∀ a b : Fin 9, ((a = 4 ∧ b ∈ ([1,2,3,6] : List (Fin 9))) ∨
       (a = 6 ∧ b ∈ ([1,2,3,5,7,8] : List (Fin 9)))) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        let ev := fun (x : Fin 9 → Bool) (p q : Bool) => C.eval (List.ofFn x ++ [p,q])
        let k := fun x : Fin 9 → Bool => x a || x b
        (∀ j ∈ [a,b], ∃ x, x j = false ∧ k x = true ∧ ev x (!x 0) false ≠ ev x (!x 0) true) →
        (∃ x, x 0 = false ∧ ev x false (k x) ≠ ev x true (k x)) →
        ∃ x, ev x (!x 0) (k x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, (1 : ℕ) ≤ x3 ∧ x3 < (9 : ℕ)) →       (4 : ℕ) ∈ x1 ∨ (6 : ℕ) ∈ x1 ∨ (7 : ℕ) ∈ x1 →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  have one (a b : Fin 9) (hc : ((a = 4 ∧ b ∈ ([1,2,3,4,6] : List (Fin 9))) ∨ (a = 6 ∧ b ∈ ([1,2,3,5,6,7,8] : List (Fin 9))))) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 13) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x a || x b]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    let k := fun x : Fin 9 → Bool => x a || x b
    let ev := fun (x : Fin 9 → Bool) (p q : Bool) => C.eval (List.ofFn x ++ [p,q])
    let f := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
    by_contra! h
    have actual (x : Fin 9 → Bool) : ev x (!x 0) (k x) = f x := by
      simpa only [ev,k,f,List.append_assoc,List.cons_append,List.nil_append,not_ne_iff] using h x
    have branch (z : Fin 9) (mem : z ∈ [a,b]) :
        ∃ x, x z = false ∧ k x = true ∧ ev x (!x 0) false ≠ ev x (!x 0) true := by
      obtain ⟨x,hx⟩ := h1 C hf hs z
      change ev x (!x 0) (x z) ≠ f x at hx
      rw [← actual x] at hx
      have sub : x z = true → k x = true := by
        intro ht
        rcases (by simpa using mem : z = a ∨ z = b) with rfl|rfl <;> simp [k,ht]
      have dh : x z ≠ k x := fun eq => hx (by rw [eq])
      cases hz : x z with
      | true => exact False.elim (dh (hz.trans (sub hz).symm))
      | false =>
        have hk : k x = true := by cases h : k x <;> simp_all only [ne_eq, not_true_eq_false, Bool.false_eq_true]
        exact ⟨x,hz,hk,by simpa only [hz,hk] using hx⟩
    have ab : a ≠ b := by
      intro eq
      obtain ⟨x,hz,hk,_⟩ := branch a (by simp)
      simp [k, ← eq, hz] at hk
    have hn : ∃ x, x 0 = false ∧ ev x false (k x) ≠ ev x true (k x) := by
      obtain ⟨x,hx⟩ := h2 C hf hs a b
      change ev x false (k x) ≠ f x at hx
      rw [← actual x] at hx
      cases hz : x 0 with
      | true => simp only [hz,Bool.not_true] at hx; exact (hx rfl).elim
      | false => exact ⟨x,hz,by simpa only [hz,Bool.not_false] using hx⟩
    have hc' : (a = 4 ∧ b ∈ ([1,2,3,6] : List (Fin 9))) ∨
        (a = 6 ∧ b ∈ ([1,2,3,5,7,8] : List (Fin 9))) := by
      rcases hc with ⟨rfl,mem⟩ | ⟨rfl,mem⟩
      · left
        exact ⟨rfl,by simpa [Ne.symm ab] using mem⟩
      · right
        exact ⟨rfl,by simpa [Ne.symm ab] using mem⟩
    obtain ⟨x,hx⟩ := h3 a b hc' C hf hs branch hn
    exact hx (actual x)
  have h1 : ∀ b ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := fun b hb => one 4 b (Or.inl ⟨rfl,hb⟩)
  have h2 : ∀ b ∈ ([1, 2, 3, 5, 6, 7, 8] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 6 || x b]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := fun b hb => one 6 b (Or.inr ⟨rfl,hb⟩)
  intro L hl hr hm C hfan hs
  have hev : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (l : List Bool), D.eval l =
      (D.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l).getD
        D.output false := fun _ _ => rfl
  have hsz : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, D.size = D.gates.length := fun _ => rfl
  -- the symmetry (1 5)(2 8)(6 7) of the graph, which fixes the vertex 0
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b0 && b5 || b5 && b8 || b8 && b3 || b3 && b4 || b4 && b0 || b0 && b1 ||
        b5 && b7 || b8 && b6 || b3 && b2 || b1 && b6 || b7 && b2 || b2 && b1) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  have hσσ : ∀ i : Fin 9, ![0, 5, 8, 3, 4, 1, 7, 6, 2] (![0, 5, 8, 3, 4, 1, 7, 6, 2] i) = i := by
    decide
  have hlt : ∀ j : ℕ, j < 9 → List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j < 9 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 9 ≤ j → List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
            (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          j false := by
    intro gs
    induction gs with
    | nil =>
      intro W W' _ _ hW j
      exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp
        omega
      · have hv : g.op.eval ((g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        by_cases hj : j < W.length
        · have hj' : List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j < W'.length := by
            by_cases h : j < 9
            · have := hlt j h
              omega
            · rw [hge j (by omega)]
              omega
          have hWj := hW j
          generalize List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j = r at hj' hWj ⊢
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hj', List.getElem?_append_left hj]
          simpa only [List.getD_eq_getElem?_getD] using hWj
        · rw [hge j (by omega)]
          by_cases hj2 : j = W.length
          · subst hj2
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
              List.getElem?_append_right (le_refl _), ← hl,
              List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  let P : Fin 9 → Fin 9 → Prop := fun u v => ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x u || x v]) ≠
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
        x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  have hsw : ∀ u v : Fin 9, P u v → P v u := by
    intro u v h D hD hDs
    obtain ⟨x, hx⟩ := h D hD hDs
    refine ⟨x, ?_⟩
    rw [Bool.or_comm]
    exact hx
  have hsy : ∀ u v : Fin 9, P u v →
      P (![0, 5, 8, 3, 4, 1, 7, 6, 2] u) (![0, 5, 8, 3, 4, 1, 7, 6, 2] v) := by
    intro u v h D hD hDs
    have hD' : PEqualNP.MetaComplexity.FanInTwo (PEqualNP.CircuitLowerBounds.Circuit.mk
        (D.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
          PEqualNP.CircuitLowerBounds.Gate.mk g.op
            (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i))
        (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] D.output D.output)) := by
      intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      refine ⟨(hD g0 hg0).1, ?_⟩
      simpa using (hD g0 hg0).2
    have hDs' : (PEqualNP.CircuitLowerBounds.Circuit.mk
        (D.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
          PEqualNP.CircuitLowerBounds.Gate.mk g.op
            (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i))
        (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] D.output D.output)).size ≤ 13 := by
      rw [hsz]
      rw [hsz] at hDs
      simpa using hDs
    obtain ⟨x, hx⟩ := h _ hD' hDs'
    · refine ⟨fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i), ?_⟩
      have e := hpre D.gates
        (List.ofFn (fun i => x (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) ++
          [!x (![0, 5, 8, 3, 4, 1, 7, 6, 2] 0)] ++
          [x (![0, 5, 8, 3, 4, 1, 7, 6, 2] (![0, 5, 8, 3, 4, 1, 7, 6, 2] u)) ||
            x (![0, 5, 8, 3, 4, 1, 7, 6, 2] (![0, 5, 8, 3, 4, 1, 7, 6, 2] v))])
        (List.ofFn x ++ [!x 0] ++ [x u || x v]) (by simp) (by simp) ?_ D.output
      · have hf := hF0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
        rw [hev] at hx
        rw [hev]
        dsimp only at hx ⊢
        rw [← e]
        intro hc
        apply hx
        rw [hc]
        exact hf
      · intro j
        by_cases hj : j < 11
        · interval_cases j
          all_goals first
            | rfl
            | (show (x u || x v) = (x (![0, 5, 8, 3, 4, 1, 7, 6, 2] (![0, 5, 8, 3, 4, 1, 7, 6, 2] u)) ||
                  x (![0, 5, 8, 3, 4, 1, 7, 6, 2] (![0, 5, 8, 3, 4, 1, 7, 6, 2] v)))
               rw [hσσ, hσσ])
        · have hj9 : List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j = j := hge j (by omega)
          rw [hj9]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hP1 : ∀ d ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), P 4 d := h1
  have hP2 : ∀ d ∈ ([1, 2, 3, 5, 6, 7, 8] : List (Fin 9)), P 6 d := h2
  have h4 : ∀ d : Fin 9, d ≠ 0 → P 4 d := by
    intro d hd
    fin_cases d
    · exact absurd rfl hd
    · exact hP1 1 (by decide)
    · exact hP1 2 (by decide)
    · exact hP1 3 (by decide)
    · exact hP1 4 (by decide)
    · exact hsy 4 1 (hP1 1 (by decide))
    · exact hP1 6 (by decide)
    · exact hsy 4 6 (hP1 6 (by decide))
    · exact hsy 4 2 (hP1 2 (by decide))
  have h6 : ∀ d : Fin 9, d ≠ 0 → P 6 d := by
    intro d hd
    fin_cases d
    · exact absurd rfl hd
    · exact hP2 1 (by decide)
    · exact hP2 2 (by decide)
    · exact hP2 3 (by decide)
    · exact hsw 4 6 (h4 6 (by decide))
    · exact hP2 5 (by decide)
    · exact hP2 6 (by decide)
    · exact hP2 7 (by decide)
    · exact hP2 8 (by decide)
  have h7 : ∀ d : Fin 9, d ≠ 0 → P 7 d := by
    intro d hd
    fin_cases d
    · exact absurd rfl hd
    · exact hsy 6 5 (hP2 5 (by decide))
    · exact hsy 6 8 (hP2 8 (by decide))
    · exact hsy 6 3 (hP2 3 (by decide))
    · exact hsw 4 7 (h4 7 (by decide))
    · exact hsy 6 1 (hP2 1 (by decide))
    · exact hsy 6 7 (hP2 7 (by decide))
    · exact hsy 6 6 (hP2 6 (by decide))
    · exact hsy 6 2 (hP2 2 (by decide))
  have allP : ∀ u v : Fin 9, u ≠ 0 → v ≠ 0 →
      (u = 4 ∨ u = 6 ∨ u = 7 ∨ v = 4 ∨ v = 6 ∨ v = 7) → P u v := by
    intro u v hu hv h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h4 v hv
    · exact h6 v hv
    · exact h7 v hv
    · exact hsw _ _ (h4 u hu)
    · exact hsw _ _ (h6 u hu)
    · exact hsw _ _ (h7 u hu)
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hl
  · simp at hl
  swap
  · simp at hl
  have ha := hr a (by simp)
  have hb := hr b (by simp)
  have hd : (⟨a, ha.2⟩ : Fin 9) = 4 ∨ (⟨a, ha.2⟩ : Fin 9) = 6 ∨ (⟨a, ha.2⟩ : Fin 9) = 7 ∨
      (⟨b, hb.2⟩ : Fin 9) = 4 ∨ (⟨b, hb.2⟩ : Fin 9) = 6 ∨ (⟨b, hb.2⟩ : Fin 9) = 7 := by
    simp only [Fin.ext_iff]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    simp
    omega
  have hu : (⟨a, ha.2⟩ : Fin 9) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hv : (⟨b, hb.2⟩ : Fin 9) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  obtain ⟨x, hx⟩ := allP _ _ hu hv hd C hfan hs
  refine ⟨x, ?_⟩
  have hga : (List.ofFn x ++ [!x 0]).getD a false = x ⟨a, ha.2⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_ofFn]
    simp [ha.2]
  have hgb : (List.ofFn x ++ [!x 0]).getD b false = x ⟨b, hb.2⟩ := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_ofFn]
    simp [hb.2]
  show C.eval (List.ofFn x ++ [!x 0] ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
    ([a, b].map fun k => (List.ofFn x ++ [!x 0]).getD k false)]) ≠ _
  have hor : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] = (u || v) := by
    intro u v
    cases u <;> cases v <;> rfl
  simp only [List.map_cons, List.map_nil, hga, hgb, hor]
  exact hx
