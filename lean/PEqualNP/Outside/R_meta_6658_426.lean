import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_6658_426
  (synthesis : ∃ C : Circuit, C.size ≤ 24 ∧ IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
    ∃ i j : ℕ, i < 14 + C.size ∧ j < 14 + C.size ∧
    let v (w b : ℕ) := wireValue C 14 (fun k => b.testBit k.val) w
    (∀ b ∈ ([130, 258, 4098, 260, 516, 8196, 136, 520, 1032, 272, 1040, 2064, 544, 2080, 4128, 1088, 4160, 8256] : List ℕ), v i b = true) ∧
    (∀ b ∈ ([127, 245, 361, 481, 595, 721, 1063, 1189, 2127, 2245, 2377, 2627, 3009, 3079, 4125, 4245, 6157, 7301, 8251, 8369, 8489, 8723, 9251, 9633, 10251, 11779, 12313, 12945, 14601, 16257] : List ℕ), v i b = false) ∧
    (∀ b ∈ ([128, 2048, 8192] : List ℕ), v j b = true) ∧ v j 6015 = false)
  (classification : (∀ x : Fin 14 → Bool,
    (∃ p l : Fin 7, p ≠ 0 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ↔
      ∀ b ∈ ([127, 245, 361, 481, 595, 721, 1063, 1189, 2127, 2245, 2377, 2627, 3009, 3079, 4125, 4245, 6157, 7301, 8251, 8369, 8489, 8723, 9251, 9633, 10251, 11779, 12313, 12945, 14601, 16257] : List ℕ), ¬ x ≤ fun k : Fin 14 => b.testBit k.val)) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (24 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ ∃ (x2 : ℕ) (x3 : ℕ), x2 < (14 : ℕ) + x1.size ∧ x3 < (14 : ℕ) + x1.size ∧ ∀ (x4 : Fin (14 : ℕ) → Bool), ((x1.wires (List.ofFn x4)).getD x2 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), x5 ≠ (0 : Fin (7 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x6) = Bool.true) ∧ ((x1.wires (List.ofFn x4)).getD x3 Bool.false = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)), ((0 : Fin (7 : ℕ)) = x5 ∨ (0 : Fin (7 : ℕ)) = x5 + (1 : Fin (7 : ℕ)) ∨ (0 : Fin (7 : ℕ)) = x5 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.natAdd (7 : ℕ) x5) = Bool.true) := by
  obtain ⟨C, hsize, hao, hnodup, i, j, hi, hj, hp, hn, hq, htop⟩ := synthesis
  have mono (w : ℕ) : Monotone (fun x : Fin 14 → Bool => wireValue C 14 x w) := by
    intro x y hxy
    let R (xs ys : List Bool) : Prop := xs.length = ys.length ∧
      ∀ k, xs.getD k false ≤ ys.getD k false
    have base : R (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp, ?_⟩
      intro k
      by_cases h : k < 14
      · have hx : k < (List.ofFn x).length := by simpa only [List.length_ofFn] using h
        have hy : k < (List.ofFn y).length := by simpa only [List.length_ofFn] using h
        rw [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy,
          List.getElem_ofFn, List.getElem_ofFn]
        exact hxy ⟨k, h⟩
      · simp [List.getD_eq_getElem?_getD, h]
    let step (xs : List Bool) (g : Gate) :=
      xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)]
    have fold (gs : List Gate) (leg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (xs ys : List Bool) (hs : R xs ys) : R (gs.foldl step xs) (gs.foldl step ys) := by
      induction gs generalizing xs ys with
      | nil => exact hs
      | cons g gs ih =>
        apply ih (fun q hq => leg q (List.mem_cons_of_mem _ hq))
        obtain ⟨hl, hv⟩ := hs
        have hg : g.op.eval (g.inputs.map fun k => xs.getD k false) ≤
            g.op.eval (g.inputs.map fun k => ys.getD k false) := by
          apply (Bool.le_iff_imp).2
          rcases leg g (by simp) with h | h
          · rw [h]
            change ((g.inputs.map _).all id = true) → ((g.inputs.map _).all id = true)
            simp only [List.all_map, Function.comp_apply, id_eq, List.all_eq_true]
            intro hx k hk
            exact Bool.eq_true_of_true_le (hx k hk ▸ hv k)
          · rw [h]
            change ((g.inputs.map _).any id = true) → ((g.inputs.map _).any id = true)
            simp only [List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
            rintro ⟨k, hk, hval⟩
            exact ⟨k, hk, Bool.eq_true_of_true_le (hval ▸ hv k)⟩
        refine ⟨by simp [step, hl], ?_⟩
        intro k
        dsimp only [step]
        by_cases hk : k < xs.length
        · rw [List.getD_append _ _ _ _ hk,
              List.getD_append _ _ _ _ (hl ▸ hk)]
          exact hv k
        · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hk),
              List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hk), hl]
          cases k - ys.length with
          | zero => exact hg
          | succ t => simp
    exact (fold C.gates hao.1 (List.ofFn x) (List.ofFn y) base).2 w
  have legal (k : ℕ) (g : Gate) (hk : C.gates[k]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧
        a ≠ b ∧ a < 14+k ∧ b < 14+k := by
    have hm := List.mem_of_getElem? hk
    have back := hao.2.1 k (List.getElem?_eq_some_iff.1 hk).1
    have atK : PEqualNP.MetaComplexity.NestedCover.gateAt C k = g := by
      change C.gates.getD k _ = g
      simp only [List.getD_eq_getElem?_getD, hk, Option.getD_some]
    rw [atK] at back
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hao.2.2 g hm)
    exact ⟨hao.1 g hm, a, b, hab, by simpa [hab] using hnodup g hm,
      back a (by simp [hab]), back b (by simp [hab])⟩
  have edges : ∀ p l : Fin 7, p ≠ 0 → (p = l ∨ p = l + 1 ∨ p = l + 3) →
      ∃ b ∈ ([130, 258, 4098, 260, 516, 8196, 136, 520, 1032, 272, 1040, 2064, 544, 2080, 4128, 1088, 4160, 8256] : List ℕ),
      ∀ k : Fin 14, b.testBit k.val = decide (k = Fin.castAdd 7 p ∨ k = Fin.natAdd 7 l) := by
    decide +kernel
  have singleton : ∀ l : Fin 7, ((0 : Fin 7) = l ∨ 0 = l + 1 ∨ 0 = l + 3) →
      ∃ b ∈ ([128, 2048, 8192] : List ℕ),
      ∀ k : Fin 14, b.testBit k.val = decide (k = Fin.natAdd 7 l) := by
    decide +kernel
  have top : ∀ k : Fin 14, Nat.testBit 6015 k.val =
      !decide (∃ l : Fin 7, ((0 : Fin 7) = l ∨ 0 = l + 1 ∨ 0 = l + 3) ∧
        k = Fin.natAdd 7 l) := by
    decide +kernel
  refine ⟨C, hsize, legal, i, j, hi, hj, fun x => ⟨?_, ?_⟩⟩
  · change wireValue C 14 x i = true ↔ _
    constructor
    · intro hx
      apply (classification x).2
      intro b hb hle
      have hf := mono i hle
      dsimp only at hf
      have hz : wireValue C 14 (fun k => b.testBit k.val) i = false := hn b hb
      rw [hx, hz] at hf
      exact (by decide : ¬ true ≤ false) hf
    · rintro ⟨p,l,hp0,he,hxp,hxl⟩
      obtain ⟨b,hb,hr⟩ := edges p l hp0 he
      have hle : (fun k : Fin 14 => b.testBit k.val) ≤ x := by
        intro k
        dsimp only
        rw [hr]
        apply Bool.le_iff_imp.2
        rintro h
        rcases of_decide_eq_true h with rfl | rfl
        · exact hxp
        · exact hxl
      have hf := mono i hle
      dsimp only at hf
      have hz : wireValue C 14 (fun k => b.testBit k.val) i = true := hp b hb
      rw [hz] at hf
      exact Bool.eq_true_of_true_le hf
  · change wireValue C 14 x j = true ↔ _
    constructor
    · intro hx
      by_contra hh
      have hle : x ≤ fun k : Fin 14 => Nat.testBit 6015 k.val := by
        intro k
        dsimp only
        rw [top]
        apply Bool.le_iff_imp.2
        intro hk
        by_cases h : ∃ l : Fin 7, ((0 : Fin 7) = l ∨ 0 = l + 1 ∨ 0 = l + 3) ∧
            k = Fin.natAdd 7 l
        · obtain ⟨l,hl,rfl⟩ := h
          exact (hh ⟨l,hl,hk⟩).elim
        · simp only [h, decide_false, Bool.not_false]
      have hf := mono j hle
      dsimp only at hf
      have hz : wireValue C 14 (fun k => Nat.testBit 6015 k.val) j = false := htop
      rw [hx, hz] at hf
      exact (by decide : ¬ true ≤ false) hf
    · rintro ⟨l,hl,hxl⟩
      obtain ⟨b,hb,hr⟩ := singleton l hl
      have hle : (fun k : Fin 14 => b.testBit k.val) ≤ x := by
        intro k
        dsimp only
        rw [hr]
        apply Bool.le_iff_imp.2
        intro h
        have eq := of_decide_eq_true h
        exact eq.symm ▸ hxl
      have hf := mono j hle
      dsimp only at hf
      have hz : wireValue C 14 (fun k => b.testBit k.val) j = true := hq b hb
      rw [hz] at hf
      exact Bool.eq_true_of_true_le hf
