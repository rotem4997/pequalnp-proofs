import Mathlib.Tactic
import PEqualNP.Defs

-- The 24 positions are the twelve edges and the twelve maximal independent sets of the Petersen
-- graph minus a vertex, so a program of ANDs and ORs reaching the target is an AND/OR circuit for
-- the edge function with first gate OR(x0, x4) and at most 15 gates. Set one of the vertices 4, 6, 7
-- of degree two to false. A gate that becomes constant, or equal to an earlier wire, is free; with
-- three free gates, 12 gates compute the edge function of the Petersen graph minus the ends of an
-- edge, against the first hypothesis (it is L-meta-2036). The second hypothesis is the rest.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2778_1
    (cofactor : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (freeThree : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 15 →
      (∃ gs, C.gates = ⟨.or, [0, 4]⟩ :: gs) → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) x) →
      ∃ (v : Fin 9) (J : Finset ℕ), (v = 4 ∨ v = 6 ∨ v = 7) ∧ 3 ≤ J.card ∧ ∀ j ∈ J, j < C.size ∧
        ∃ (a b : Bool), ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
          (C.wires (List.ofFn x)).getD (9 + j) false = (a && (C.wires (List.ofFn x)).getD k false || b)) :
    have x1 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))]; ∀ (x2 : List (BitVec (24 : ℕ))), x2.length ≤ (14 : ℕ) → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ x1 ++ List.take x4 x2 ∧ ∃ x6 ∈ x1 ++ List.take x4 x2, ∃ x7 ∈ x1 ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) → (3428671 : BitVec (24 : ℕ)) ∉ x1 ++ x2 := by
  classical
  have wnil : ∀ (o : ℕ) (x : List Bool), PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[], o⟩ x = x := fun _ _ => rfl
  have wsnoc : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
        [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
    fun gs g o x => List.foldl_append
  have fnil : PEqualNP.MetaComplexity.FanInTwo ⟨[], 0⟩ := fun g hg => absurd hg List.not_mem_nil
  have fone : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (l : List ℕ),
      (op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ op = PEqualNP.CircuitLowerBounds.GateOp.not) → l.length ≤ 2 → PEqualNP.MetaComplexity.FanInTwo ⟨[⟨op, l⟩], 0⟩ := by
    intro op l h hl a ha
    obtain rfl := List.mem_singleton.1 ha
    exact ⟨h, hl⟩
  -- facts about running a list of gates
  have run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : List Bool),
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length ∧
      (∀ i < x.length, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false) ∧
      ∀ (j : ℕ) (h : j < gs.length), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD (x.length + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun i => if i < x.length + j then
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false else false) := by
    intro gs o x
    induction gs using List.reverseRecOn with
    | nil => refine ⟨by rw [wnil]; simp, fun i _ => by rw [wnil], fun j h => absurd h (Nat.not_lt_zero _)⟩
    | append_singleton gs g ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have e : PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g], o⟩ x =
          PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x ++
            [g.op.eval (g.inputs.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x).getD i false)] :=
        wsnoc gs g o x
      rw [e]
      generalize PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, o⟩ x = W at h1 h2 h3 ⊢
      generalize hval : g.op.eval (g.inputs.map fun i => W.getD i false) = val
      have old : ∀ i < W.length, (W ++ [val]).getD i false = W.getD i false := fun i hi =>
        List.getD_append _ _ _ _ hi
      refine ⟨by simp [h1]; omega, fun i hi => by rw [old i (by omega)]; exact h2 i hi, ?_⟩
      intro j hj
      rcases Nat.lt_or_ge j gs.length with hlt | hge
      · rw [old _ (by omega), h3 j hlt, List.getElem_append_left hlt]
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · rfl
      · have hj' : j = gs.length := by simp at hj; omega
        subst hj'
        rw [← h1, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero, List.getElem_concat_length]
        refine hval.symm.trans ?_
        congr 1
        apply List.map_congr_left
        intro i _
        split
        · rw [old i (by omega)]
        · exact List.getD_eq_default _ _ (by omega)
  show ∀ (x2 : List (BitVec 24)), x2.length ≤ 14 → (∀ (x4 : ℕ) (x5 : x4 < x2.length), x2[x4] ∉ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ List.take x4 x2 ∧
    ∃ x6 ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ List.take x4 x2, ∃ x7 ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ List.take x4 x2, x2[x4] = x6 &&& x7 ∨ x2[x4] = x6 ||| x7) →
    3428671#24 ∉ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ x2
  intro xs hlen hstep hmem
  let bb : Fin 9 → BitVec 24 := ![4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24]
  let row : ℕ → Fin 9 → Bool := fun r i => (bb i).getLsbD r
  have e0 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 0 false = (4358697#24).getLsbD r := by
    intro r _
    rfl
  have e1 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 1 false = (8397251#24).getLsbD r := by
    intro r _
    rfl
  have e2 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 2 false = (662022#24).getLsbD r := by
    intro r _
    rfl
  have e3 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 3 false = (304212#24).getLsbD r := by
    intro r _
    rfl
  have e4 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 4 false = (8980632#24).getLsbD r := by
    intro r _
    rfl
  have e5 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 5 false = (1068256#24).getLsbD r := by
    intro r _
    rfl
  have e6 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 6 false = (2199296#24).getLsbD r := by
    intro r _
    rfl
  have e7 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 7 false = (12709888#24).getLsbD r := by
    intro r _
    rfl
  have e8 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 8 false = (16646144#24).getLsbD r := by
    intro r _
    rfl
  have e9 : ∀ r < 24, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD 9 false = (13339321#24).getLsbD r := by
    intro r _
    show ((4358697#24).getLsbD r || ((8980632#24).getLsbD r || false)) = _
    rw [Bool.or_false, ← BitVec.getLsbD_or, show 4358697#24 ||| 8980632#24 = 13339321#24 by decide]
  have l0 : ∀ a ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24], a = 0#24 ∨ a = 16777215#24 ∨ ∃ w < 10, ∀ r < 24,
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨[(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate)], 0⟩ (List.ofFn (row r))).getD w false = a.getLsbD r := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0, by norm_num, e0⟩)
    · exact Or.inr (Or.inr ⟨1, by norm_num, e1⟩)
    · exact Or.inr (Or.inr ⟨2, by norm_num, e2⟩)
    · exact Or.inr (Or.inr ⟨3, by norm_num, e3⟩)
    · exact Or.inr (Or.inr ⟨4, by norm_num, e4⟩)
    · exact Or.inr (Or.inr ⟨5, by norm_num, e5⟩)
    · exact Or.inr (Or.inr ⟨6, by norm_num, e6⟩)
    · exact Or.inr (Or.inr ⟨7, by norm_num, e7⟩)
    · exact Or.inr (Or.inr ⟨8, by norm_num, e8⟩)
    · exact Or.inr (Or.inr ⟨9, by norm_num, e9⟩)
  have rows0 : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool, bif ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) then (List.range 24).any (fun r => Nat.testBit 3428671 r && ((!(Nat.testBit 4358697 r) || a0) && (!(Nat.testBit 8397251 r) || a1) && (!(Nat.testBit 662022 r) || a2) && (!(Nat.testBit 304212 r) || a3) && (!(Nat.testBit 8980632 r) || a4) && (!(Nat.testBit 1068256 r) || a5) && (!(Nat.testBit 2199296 r) || a6) && (!(Nat.testBit 12709888 r) || a7) && (!(Nat.testBit 16646144 r) || a8)))
      else (List.range 24).any (fun r => !(Nat.testBit 3428671 r) && ((!a0 || Nat.testBit 4358697 r) && (!a1 || Nat.testBit 8397251 r) && (!a2 || Nat.testBit 662022 r) && (!a3 || Nat.testBit 304212 r) && (!a4 || Nat.testBit 8980632 r) && (!a5 || Nat.testBit 1068256 r) && (!a6 || Nat.testBit 2199296 r) && (!a7 || Nat.testBit 12709888 r) && (!a8 || Nat.testBit 16646144 r))) := by
    decide +kernel
  have rows : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      ((fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = true → ∃ r < 24, (3428671#24).getLsbD r = true ∧
        ∀ i : Fin 9, row r i = true → (![a0, a1, a2, a3, a4, a5, a6, a7, a8] : Fin 9 → Bool) i = true) ∧
      ((fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = false → ∃ r < 24, (3428671#24).getLsbD r = false ∧
        ∀ i : Fin 9, (![a0, a1, a2, a3, a4, a5, a6, a7, a8] : Fin 9 → Bool) i = true → row r i = true) := by
    intro a0 a1 a2 a3 a4 a5 a6 a7 a8
    have h := rows0 a0 a1 a2 a3 a4 a5 a6 a7 a8
    have hF : (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = ((a0 && a1) || (a1 && a2) || (a2 && a3) || (a3 && a4) || (a4 && a0) || (a0 && a5) || (a1 && a6) || (a2 && a7) || (a3 && a8) || (a5 && a7) || (a6 && a8) || (a8 && a5)) := rfl
    have imp1 : ∀ p q : Bool, (!p || q) = true → p = true → q = true := by decide
    constructor
    · intro hT
      rw [hF] at hT
      rw [hT, cond_true] at h
      obtain ⟨r, hr, h1⟩ := List.any_eq_true.1 h
      obtain ⟨h2, h3⟩ := Bool.and_eq_true_iff.1 h1
      simp only [Bool.and_eq_true] at h3
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := h3
      refine ⟨r, List.mem_range.1 hr, h2, fun i => ?_⟩
      fin_cases i
      · exact imp1 _ _ k0
      · exact imp1 _ _ k1
      · exact imp1 _ _ k2
      · exact imp1 _ _ k3
      · exact imp1 _ _ k4
      · exact imp1 _ _ k5
      · exact imp1 _ _ k6
      · exact imp1 _ _ k7
      · exact imp1 _ _ k8
    · intro hT
      rw [hF] at hT
      rw [hT, cond_false] at h
      obtain ⟨r, hr, h1⟩ := List.any_eq_true.1 h
      obtain ⟨h2, h3⟩ := Bool.and_eq_true_iff.1 h1
      simp only [Bool.and_eq_true] at h3
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨k0, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩, k7⟩, k8⟩ := h3
      refine ⟨r, List.mem_range.1 hr, (show ∀ p : Bool, (!p) = true → p = false by decide) _ h2, fun i => ?_⟩
      fin_cases i
      · exact imp1 _ _ k0
      · exact imp1 _ _ k1
      · exact imp1 _ _ k2
      · exact imp1 _ _ k3
      · exact imp1 _ _ k4
      · exact imp1 _ _ k5
      · exact imp1 _ _ k6
      · exact imp1 _ _ k7
      · exact imp1 _ _ k8
  have len1 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 9 → Bool), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length = 9 + gs.length := by
    intro gs x
    have := (run gs 0 (List.ofFn x)).1
    rwa [List.length_ofFn] at this
  have build : ∀ k ≤ xs.length, ∃ gs : List PEqualNP.CircuitLowerBounds.Gate, gs.length = k ∧ PEqualNP.MetaComplexity.Monotone2 ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, 0⟩ ∧
      ∀ a ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ xs.take k, a = 0#24 ∨ a = 16777215#24 ∨ ∃ w < 10 + k, ∀ r < 24,
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, 0⟩ (List.ofFn (row r))).getD w false = a.getLsbD r := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], rfl, ?_, ?_⟩
      · intro g hg
        obtain rfl := List.mem_singleton.1 hg
        exact ⟨Or.inr rfl, le_refl _⟩
      · intro a ha
        rw [List.take_zero, List.append_nil] at ha
        exact l0 a ha
    | succ k ih =>
      intro hk
      obtain ⟨gs, hgl, hgm, hga⟩ := ih (by omega)
      obtain ⟨hnew, c, hc, e, he, hce⟩ := hstep k (by omega)
      have h0 : 0#24 ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ xs.take k := by simp
      have h1 : 16777215#24 ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ xs.take k := by simp
      have andone : ∀ a : BitVec 24, a &&& 16777215#24 = a := fun a => BitVec.and_allOnes
      have orone : ∀ a : BitVec 24, a ||| 16777215#24 = 16777215#24 := fun a => BitVec.or_allOnes
      have real : ∀ a ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ xs.take k, ∀ a' ∈ [0#24, 16777215#24, 4358697#24, 8397251#24, 662022#24, 304212#24, 8980632#24, 1068256#24, 2199296#24, 12709888#24, 16646144#24, 13339321#24] ++ xs.take k,
          (xs[k] = a &&& a' ∨ xs[k] = a ||| a') → ∃ w < 10 + k, ∀ r < 24,
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, 0⟩ (List.ofFn (row r))).getD w false = a.getLsbD r := by
        intro a ha a' ha' h
        rcases hga a ha with rfl | rfl | h2
        · exfalso
          rcases h with h | h
          · rw [BitVec.zero_and] at h
            exact hnew (h ▸ h0)
          · rw [BitVec.zero_or] at h
            exact hnew (h ▸ ha')
        · exfalso
          rcases h with h | h
          · rw [BitVec.and_comm, andone] at h
            exact hnew (h ▸ ha')
          · rw [BitVec.or_comm, orone] at h
            exact hnew (h ▸ h1)
        · exact h2
      obtain ⟨wc, hwc, hc'⟩ := real c hc e he hce
      obtain ⟨we, hwe, he'⟩ := real e he c hc (by rwa [BitVec.and_comm, BitVec.or_comm])
      have hlen2 : ∀ x : Fin 9 → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, 0⟩ (List.ofFn x)).length = 10 + k := by
        intro x
        rw [len1, List.length_cons, hgl]
        omega
      obtain ⟨op, hop, hval⟩ : ∃ op : PEqualNP.CircuitLowerBounds.GateOp, (op = .and ∨ op = .or) ∧ ∀ r < 24,
          op.eval [c.getLsbD r, e.getLsbD r] = (xs[k]).getLsbD r := by
        rcases hce with h | h
        · refine ⟨.and, Or.inl rfl, fun r _ => ?_⟩
          rw [h, BitVec.getLsbD_and]
          show (c.getLsbD r && (e.getLsbD r && true)) = _
          rw [Bool.and_true]
        · refine ⟨.or, Or.inr rfl, fun r _ => ?_⟩
          rw [h, BitVec.getLsbD_or]
          show (c.getLsbD r || (e.getLsbD r || false)) = _
          rw [Bool.or_false]
      refine ⟨gs ++ [⟨op, [wc, we]⟩], by rw [List.length_append, hgl]; rfl, ?_, ?_⟩
      · intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · exact hgm _ List.mem_cons_self
        · rcases List.mem_append.1 hg with hg | hg
          · exact hgm g (List.mem_cons_of_mem _ hg)
          · obtain rfl := List.mem_singleton.1 hg
            exact ⟨hop, le_refl _⟩
      · have hw := fun r : ℕ => wsnoc ((⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs) ⟨op, [wc, we]⟩ 0 (List.ofFn (row r))
        have old : ∀ a : BitVec 24, (a = 0#24 ∨ a = 16777215#24 ∨ ∃ w < 10 + k, ∀ r < 24,
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, 0⟩ (List.ofFn (row r))).getD w false = a.getLsbD r) →
            a = 0#24 ∨ a = 16777215#24 ∨ ∃ w < 10 + (k + 1), ∀ r < 24,
            (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: (gs ++ [⟨op, [wc, we]⟩]), 0⟩ (List.ofFn (row r))).getD w false = a.getLsbD r := by
          rintro a (h | h | ⟨w, hw1, hw2⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · refine Or.inr (Or.inr ⟨w, by omega, fun r hr => ?_⟩)
            rw [← hw2 r hr]
            refine (congrArg (fun l => List.getD l w false) (hw r)).trans ?_
            exact List.getD_append _ _ _ _ (by rw [hlen2]; exact hw1)
        intro a ha
        rw [List.take_succ_eq_append_getElem (by omega), ← List.append_assoc] at ha
        rcases List.mem_append.1 ha with ha | ha
        · exact old a (hga a ha)
        · obtain rfl := List.mem_singleton.1 ha
          refine Or.inr (Or.inr ⟨10 + k, by omega, fun r hr => ?_⟩)
          refine (congrArg (fun l => List.getD l (10 + k) false) (hw r)).trans ?_
          rw [← hval r hr, ← hc' r hr, ← he' r hr]
          refine (List.getD_append_right _ _ _ _ (by rw [hlen2])).trans ?_
          rw [hlen2, Nat.sub_self, List.getD_cons_zero]
          rfl
  obtain ⟨gs, hgl, hmono0, hga⟩ := build xs.length (le_refl _)
  rw [List.take_length] at hga
  obtain ⟨o, hoR⟩ : ∃ o, ∀ r < 24,
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, 0⟩ (List.ofFn (row r))).getD o false = (3428671#24).getLsbD r := by
    rcases hga _ hmem with h | h | ⟨w, _, h⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨w, h⟩
  obtain ⟨C, hCd⟩ : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨(⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs, o⟩ := ⟨_, rfl⟩
  have hmono : PEqualNP.MetaComplexity.Monotone2 C := by rw [hCd]; exact hmono0
  have hCr : ∀ r < 24, C.eval (List.ofFn (row r)) = (3428671#24).getLsbD r := by rw [hCd]; exact hoR
  have hsz0 : C.size ≤ 15 := by
    rw [hCd]
    show ((⟨.or, [0, 4]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: gs).length ≤ 15
    rw [List.length_cons, hgl]
    omega
  have hgates : ∃ gs, C.gates = ⟨.or, [0, 4]⟩ :: gs := ⟨gs, by rw [hCd]⟩
  have mono : ∀ x z : Fin 9 → Bool, x ≤ z → C.eval (List.ofFn x) = true → C.eval (List.ofFn z) = true := by
    intro x z hxz
    have key : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        ∀ i, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false = true →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false = true := by
      intro gs
      induction gs using List.reverseRecOn with
      | nil =>
        intro _ i h
        rw [wnil] at h ⊢
        rcases Nat.lt_or_ge i 9 with hi | hi
        · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn] at h ⊢
          have := hxz ⟨i, hi⟩
          rw [h] at this
          exact le_antisymm (Bool.le_true _) this
        · rw [List.getD_eq_default _ _ (by simpa using hi)] at h
          exact absurd h (by simp)
      | append_singleton gs g ih =>
        intro hg i h
        have ih' := ih (fun a ha => hg a (List.mem_append_left _ ha))
        have hgop := hg g (List.mem_append_right _ List.mem_cons_self)
        have l1 := (run gs 0 (List.ofFn x)).1
        have l2 := (run gs 0 (List.ofFn z)).1
        rw [List.length_ofFn] at l1 l2
        rw [wsnoc] at h ⊢
        rcases Nat.lt_trichotomy i (9 + gs.length) with hi | hi | hi
        · rw [List.getD_append _ _ _ _ (by omega)] at h ⊢
          exact ih' i h
        · rw [List.getD_append_right _ _ _ _ (by omega), show i - (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).length = 0 by omega] at h
          rw [List.getD_append_right _ _ _ _ (by omega), show i - (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = 0 by omega]
          rw [List.getD_cons_zero] at h ⊢
          obtain ⟨op, l⟩ := g
          rcases hgop with hop | hop
          · subst hop
            have h' : (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).all id = true := h
            show (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false).all id = true
            simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, id] at h' ⊢
            exact fun a ha => ih' a (h' a ha)
          · subst hop
            have h' : (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).any id = true := h
            show (l.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false).any id = true
            simp only [List.any_eq_true, List.mem_map, id] at h' ⊢
            obtain ⟨b, ⟨a, ha, hab⟩, hb⟩ := h'
            exact ⟨_, ⟨a, ha, rfl⟩, ih' a (hab.trans hb)⟩
        · rw [List.getD_eq_default _ _ (by rw [List.length_append, l1]; simp; omega)] at h
          exact absurd h (by simp)
    exact key C.gates (fun g hg => (hmono g hg).1) C.output
  have hcomp' : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) x := by
    intro x
    obtain ⟨t1, t2⟩ := rows (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
    have hx : (![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] : Fin 9 → Bool) = x := by
      funext i
      fin_cases i <;> rfl
    rw [hx] at t1 t2
    cases hF : (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) x with
    | true =>
      obtain ⟨r, hr, h1, h2⟩ := t1 hF
      exact mono (row r) x (fun i => Bool.le_iff_imp.2 (h2 i)) ((hCr r hr).trans h1)
    | false =>
      obtain ⟨r, hr, h1, h2⟩ := t2 hF
      by_contra hne
      have h3 := mono x (row r) (fun i => Bool.le_iff_imp.2 (h2 i)) (by simpa using hne)
      rw [hCr r hr, h1] at h3
      exact absurd h3 (by decide)
  have hcomp : (fun x : Fin 9 → Bool => C.eval (List.ofFn x)) = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := funext hcomp'
  have hfan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨v, J, hv, hcard, hJ⟩ := freeThree C hmono hsz0 hgates hcomp'
  apply cofactor
  let σ : Fin 9 → Fin 9 → Fin 8 := ![0, 0, 0, 0, ![0, 1, 2, 3, 0, 4, 5, 6, 7], 0, ![1, 0, 4, 7, 5, 2, 0, 6, 3],
    ![1, 2, 3, 7, 5, 0, 6, 0, 4], 0]
  let X : (Fin 8 → Bool) → Fin 9 → Bool := fun y i => if i = v then false else y (σ v i)
  have hX : ∀ y, X y v = false := fun y => by simp [X]
  have hrestr : ∀ y, C.eval (List.ofFn (X y)) = (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) y := by
    intro y
    refine (congrFun hcomp (X y)).trans ?_
    have key : ∀ a : Fin 8 → Bool, (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) (fun i => if i = v then false else a (σ v i)) = (fun x : Fin 8 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) a := by
      intro a
      rcases hv with rfl | rfl | rfl <;> simp [σ] <;> ac_rfl
    exact key y
  let W : (Fin 8 → Bool) → ℕ → Bool := fun y i => (C.wires (List.ofFn (X y))).getD i false
  have hW0 : ∀ y (i : Fin 9), W y i = X y i := by
    intro y i
    have := (run C.gates C.output (List.ofFn (X y))).2.1 i (by simp)
    refine this.trans ?_
    rw [List.getD_eq_getElem _ _ (by simp)]
    exact List.getElem_ofFn (by simp)
  have hWg : ∀ y (j : ℕ) (h : j < C.gates.length), W y (9 + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => if i < 9 + j then W y i else false) := by
    intro y j h
    have := (run C.gates C.output (List.ofFn (X y))).2.2 j h
    rw [List.length_ofFn] at this
    exact this
  have hWout : ∀ y i, 9 + C.gates.length ≤ i → W y i = false := by
    intro y i hi
    have := (run C.gates C.output (List.ofFn (X y))).1
    rw [List.length_ofFn] at this
    exact List.getD_eq_default _ _ (this.le.trans hi)
  -- a gate on constants and kept wires is constant or a gate on kept wires
  have hall : ∀ (A U : (Fin 8 → Bool) → ℕ → Bool) (m : ℕ) (l : List ℕ),
      (∀ i ∈ l, (∃ b, ∀ y, A y i = b) ∨ ∃ k < m, ∀ y, A y i = U y k) →
      (∀ y, (l.map (A y)).all id = false) ∨
        ∃ l' : List ℕ, l'.length ≤ l.length ∧ ∀ y, (l.map (A y)).all id = (l'.map (U y)).all id := by
    intro A U m l
    induction l with
    | nil => intro _; exact Or.inr ⟨[], by simp⟩
    | cons i l ih =>
      intro h
      rcases ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) with h0 | ⟨l', hl, he⟩
      · left; intro y; simp only [List.map_cons, List.all_cons, h0 y, Bool.and_false]
      rcases h i List.mem_cons_self with ⟨b, hb⟩ | ⟨k, hk, hb⟩
      · cases b
        · left; intro y; simp only [List.map_cons, List.all_cons, hb y, id, Bool.false_and]
        · exact Or.inr ⟨l', by simp; omega, fun y => by
            rw [List.map_cons, List.all_cons, hb y, he y]; simp⟩
      · exact Or.inr ⟨k :: l', by simpa using hl, fun y => by
          rw [List.map_cons, List.all_cons, hb y, he y, List.map_cons, List.all_cons]⟩
  have hany : ∀ (A U : (Fin 8 → Bool) → ℕ → Bool) (m : ℕ) (l : List ℕ),
      (∀ i ∈ l, (∃ b, ∀ y, A y i = b) ∨ ∃ k < m, ∀ y, A y i = U y k) →
      (∀ y, (l.map (A y)).any id = true) ∨
        ∃ l' : List ℕ, l'.length ≤ l.length ∧ ∀ y, (l.map (A y)).any id = (l'.map (U y)).any id := by
    intro A U m l
    induction l with
    | nil => intro _; exact Or.inr ⟨[], by simp⟩
    | cons i l ih =>
      intro h
      rcases ih (fun k hk => h k (List.mem_cons_of_mem _ hk)) with h0 | ⟨l', hl, he⟩
      · left; intro y; simp only [List.map_cons, List.any_cons, h0 y, Bool.or_true]
      rcases h i List.mem_cons_self with ⟨b, hb⟩ | ⟨k, hk, hb⟩
      · cases b
        · exact Or.inr ⟨l', by simp; omega, fun y => by
            rw [List.map_cons, List.any_cons, hb y, he y]; simp⟩
        · left; intro y; simp only [List.map_cons, List.any_cons, hb y, id, Bool.true_or]
      · exact Or.inr ⟨k :: l', by simpa using hl, fun y => by
          rw [List.map_cons, List.any_cons, hb y, he y, List.map_cons, List.any_cons]⟩
  have main : ∀ k ≤ C.gates.length, ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
      PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k)).card ≤ k ∧
      ∀ i < 9 + k, (∃ b, ∀ y, W y i = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
        W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fnil, by simp, ?_⟩
      intro i hi
      have hw : ∀ y, W y i = X y ⟨i, by omega⟩ := fun y => hW0 y ⟨i, by omega⟩
      by_cases hv : (⟨i, by omega⟩ : Fin 9) = v
      · exact Or.inl ⟨false, fun y => by rw [hw, hv, hX]⟩
      · refine Or.inr ⟨σ v ⟨i, by omega⟩, by simp, fun y => ?_⟩
        rw [hw]
        have hl := List.getElem_ofFn (f := y) (i := (σ v ⟨i, by omega⟩ : ℕ)) (by simp)
        simp only [X, hv, ite_false, wnil]
        rw [List.getD_eq_getElem _ _ (by simp)]
        exact hl.symm
    | succ k ih =>
      intro hk
      obtain ⟨gs, hgf, hgc, hgi⟩ := ih (by omega)
      have hfilt : (J.filter (· < k + 1)).card ≤ (J.filter (· < k)).card + (if k ∈ J then 1 else 0) := by
        have hsub : J.filter (· < k + 1) ⊆ J.filter (· < k) ∪ (if k ∈ J then {k} else ∅) := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_union] at ha ⊢
          rcases Nat.lt_or_ge a k with h | h
          · exact Or.inl ⟨ha.1, h⟩
          · have : a = k := by omega
            subst this
            right; simp [ha.1]
        refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
        split <;> simp
      -- wire `9 + k` is constant, kept already, or one new gate away
      have keep : ((∃ b, ∀ y, W y (9 + k) = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
            W y (9 + k) = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false) →
          ∃ gs : List PEqualNP.CircuitLowerBounds.Gate,
          PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧ gs.length + (J.filter (· < k + 1)).card ≤ k + 1 ∧
          ∀ i < 9 + (k + 1), (∃ b, ∀ y, W y i = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
            W y i = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
        intro h
        refine ⟨gs, hgf, ?_, ?_⟩
        · split at hfilt <;> omega
        · intro i hi
          rcases Nat.lt_or_ge i (9 + k) with h' | h'
          · exact hgi i h'
          · have : i = 9 + k := by omega
            subst this; exact h
      by_cases hkJ : k ∈ J
      · apply keep
        obtain ⟨a, b, i, hi, hb⟩ := (hJ k hkJ).2
        have hb' : ∀ y, W y (9 + k) = (a && W y i || b) := fun y => hb (X y) (hX y)
        cases b with
        | true => exact Or.inl ⟨true, fun y => by rw [hb']; simp⟩
        | false =>
          cases a with
          | false => exact Or.inl ⟨false, fun y => by rw [hb']; simp⟩
          | true =>
            have hb'' : ∀ y, W y (9 + k) = W y i := fun y => by rw [hb']; simp
            rcases hgi i hi with ⟨c, hc⟩ | ⟨j, hj, hc⟩
            · exact Or.inl ⟨c, fun y => (hb'' y).trans (hc y)⟩
            · exact Or.inr ⟨j, hj, fun y => (hb'' y).trans (hc y)⟩
      · have hmem : C.gates[k] ∈ C.gates := List.getElem_mem _
        have hg := hfan _ hmem
        have hWk := fun y => hWg y k (by omega)
        generalize C.gates[k] = g at hg hWk
        let U : (Fin 8 → Bool) → ℕ → Bool := fun y j =>
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false
        let A : (Fin 8 → Bool) → ℕ → Bool := fun y i => if i < 9 + k then W y i else false
        have hA : ∀ i, (∃ b, ∀ y, A y i = b) ∨ ∃ j < 8 + gs.length, ∀ y, A y i = U y j := by
          intro i
          by_cases h : i < 9 + k
          · simpa [A, h, U] using hgi i h
          · exact Or.inl ⟨false, fun y => by simp [A, h]⟩
        have hWA : ∀ y, W y (9 + k) = g.op.eval (g.inputs.map (A y)) := hWk
        have hnew : (∃ b, ∀ y, W y (9 + k) = b) ∨ ∃ g' : PEqualNP.CircuitLowerBounds.Gate,
            PEqualNP.MetaComplexity.FanInTwo ⟨[g'], 0⟩ ∧ ∀ y, W y (9 + k) = g'.op.eval (g'.inputs.map (U y)) := by
          obtain ⟨op, l⟩ := g
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
          obtain ⟨hop, hlen⟩ := hg
          rcases hop with rfl | rfl | rfl
          · rcases hall A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
            · exact Or.inl ⟨false, fun y => (hWA y).trans (h y)⟩
            · exact Or.inr ⟨⟨.and, l'⟩, fone _ _ (Or.inl rfl) (h1.trans hlen), fun y => (hWA y).trans (h3 y)⟩
          · rcases hany A U _ l (fun i _ => hA i) with h | ⟨l', h1, h3⟩
            · exact Or.inl ⟨true, fun y => (hWA y).trans (h y)⟩
            · exact Or.inr ⟨⟨.or, l'⟩, fone _ _ (Or.inr (Or.inl rfl)) (h1.trans hlen), fun y => (hWA y).trans (h3 y)⟩
          · cases l with
            | nil => exact Or.inl ⟨true, fun y => by rw [hWA]; rfl⟩
            | cons i l =>
              rcases hA i with ⟨b, hb⟩ | ⟨j, _, hb⟩
              · exact Or.inl ⟨!b, fun y => by rw [hWA, ← hb y]; rfl⟩
              · exact Or.inr ⟨⟨.not, [j]⟩, fone _ _ (Or.inr (Or.inr rfl)) (by simp), fun y => by
                  rw [hWA]; show (!(A y i)) = !(U y j); rw [hb y]⟩
        rcases hnew with h | ⟨g', hg', hv⟩
        · exact keep (Or.inl h)
        have step : ∀ y : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs ++ [g'], 0⟩ (List.ofFn y) =
            PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y) ++ [g'.op.eval (g'.inputs.map (U y))] := by
          intro y
          exact wsnoc gs g' 0 _
        have hlen : ∀ y : Fin 8 → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).length = 8 + gs.length := by
          intro y
          have := (run gs 0 (List.ofFn y)).1
          rwa [List.length_ofFn] at this
        refine ⟨gs ++ [g'], ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_append.1 ha with h | h
          · exact hgf a h
          · exact hg' a h
        · simp only [hkJ, ite_false] at hfilt
          simp only [List.length_append, List.length_singleton]
          omega
        · intro i hi
          rcases Nat.lt_or_ge i (9 + k) with h' | h'
          · rcases hgi i h' with h | ⟨j, hj, h⟩
            · exact Or.inl h
            · refine Or.inr ⟨j, by simp; omega, fun y => ?_⟩
              rw [step, List.getD_append _ _ _ _ (by rw [hlen]; exact hj)]
              exact h y
          · have : i = 9 + k := by omega
            subst this
            refine Or.inr ⟨8 + gs.length, by simp, fun y => ?_⟩
            rw [step, List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
            simpa using hv y
  obtain ⟨gs, hgf, hgc, hgi⟩ := main C.gates.length (le_refl _)
  have hJf : J.filter (· < C.gates.length) = J := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact (hJ j hj).1
  rw [hJf] at hgc
  have hsz : C.gates.length ≤ 15 := hsz0
  have hout : (∃ b, ∀ y, W y C.output = b) ∨ ∃ j < 8 + gs.length, ∀ y : Fin 8 → Bool,
      W y C.output = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD j false := by
    rcases Nat.lt_or_ge C.output (9 + C.gates.length) with h | h
    · exact hgi _ h
    · exact Or.inl ⟨false, fun y => hWout y _ h⟩
  rcases hout with ⟨b, hb⟩ | ⟨j, _, hb⟩
  · exfalso
    have e1 := (hrestr (fun _ => true)).symm.trans (hb (fun _ => true))
    have e0 := (hrestr (fun _ => false)).symm.trans (hb (fun _ => false))
    simp at e1 e0
    exact absurd (e1.symm.trans e0) (by simp)
  · refine ⟨⟨gs, j⟩, hgf, ?_, fun y => ?_⟩
    · show gs.length ≤ 12
      omega
    · rw [← hrestr y]
      exact (hb y).symm
